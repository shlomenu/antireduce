open Core

type t =
  { universe: int
  ; void: int
  ; space2int: (Version_space.t, int) Hashtbl.t
  ; int2space: Version_space.t Array_list.t
  ; inversions: int option Array_list.t
  ; n_step: (int * int, int) Hashtbl.t
  ; substitutions: (int * int, (int, int) Hashtbl.t) Hashtbl.t }

let version_of_int tbl = Array_list.get tbl.int2space

let size_of_version_tbl tbl = tbl.int2space.occupancy

let clear_dyn_prog_tbls tbl =
  Hashtbl.clear tbl.n_step ;
  Hashtbl.clear tbl.substitutions

let deallocate_versions tbl =
  clear_dyn_prog_tbls tbl ;
  Hashtbl.clear tbl.space2int ;
  Array_list.clear tbl.int2space ;
  Array_list.clear tbl.inversions

let rec string_of_version_tbl tbl i =
  match version_of_int tbl i with
  | Universe ->
      "U"
  | Void ->
      "Void"
  | ApplySpace (f, x) ->
      Printf.sprintf "@(%s, %s)"
        (string_of_version_tbl tbl f)
        (string_of_version_tbl tbl x)
  | AbstractionSpace b ->
      Printf.sprintf "abs(%s)" (string_of_version_tbl tbl b)
  | IndexSpace i ->
      Printf.sprintf "$%d" i
  | TerminalSpace p ->
      Program.to_string p
  | Union u ->
      let s =
        String.concat ~sep:"; " @@ List.map u ~f:(string_of_version_tbl tbl)
      in
      Printf.sprintf "{%s}" s

let incorporate_space tbl v =
  match Hashtbl.find tbl.space2int v with
  | Some v ->
      v
  | None ->
      let i = tbl.int2space.occupancy in
      Hashtbl.set tbl.space2int ~key:v ~data:i ;
      Array_list.push tbl.int2space v ;
      Array_list.push tbl.inversions None ;
      i

let create () =
  let tbl =
    { void= 0
    ; universe= 1
    ; space2int= Hashtbl.create (module Version_space)
    ; int2space= Array_list.create ()
    ; substitutions= Hashtbl.create (module Util.IntPair)
    ; n_step= Hashtbl.create (module Util.IntPair)
    ; inversions= Array_list.create () }
  in
  assert (incorporate_space tbl Void = tbl.void) ;
  assert (incorporate_space tbl Universe = tbl.universe) ;
  tbl

let version_of_apply tbl f x =
  if f = tbl.void || x = tbl.void then tbl.void
  else incorporate_space tbl (ApplySpace (f, x))

let version_of_abstraction tbl b =
  if b = tbl.void then tbl.void else incorporate_space tbl (AbstractionSpace b)

let version_of_index tbl i = incorporate_space tbl (IndexSpace i)

let version_of_terminal tbl p = incorporate_space tbl (TerminalSpace p)

let union tbl spaces =
  if List.mem spaces tbl.universe ~equal then tbl.universe
  else
    let spaces =
      List.dedup_and_sort ~compare:( - )
      @@ List.concat_map spaces ~f:(fun space ->
             match version_of_int tbl space with
             | Union spaces' ->
                 spaces'
             | Void ->
                 []
             | Universe ->
                 let msg =
                   "union: impossible: already checked that "
                   ^ "universe is not in this list"
                 in
                 failwith msg
             | _ ->
                 [space] )
    in
    match spaces with
    | [v] ->
        v
    | [] ->
        tbl.void
    | _ ->
        incorporate_space tbl (Union spaces)

let rec incorporate tbl : Program.t -> int = function
  | Index i ->
      version_of_index tbl i
  | Abstraction b ->
      version_of_abstraction tbl @@ incorporate tbl b
  | Apply (f, x) ->
      version_of_apply tbl (incorporate tbl f) (incorporate tbl x)
  | (Primitive _ | Invented _) as p ->
      version_of_terminal tbl p

(* returned list is length 1 unless unions of length > 1 are recursively
     present at some level of the version space *)
let rec extract tbl i =
  match version_of_int tbl i with
  | Union u ->
      List.concat_map u ~f:(extract tbl)
  | ApplySpace (f, x) ->
      extract tbl f
      |> List.concat_map ~f:(fun f' ->
             extract tbl x |> List.map ~f:(fun x' -> Program.Apply (f', x')) )
  | IndexSpace i ->
      [Index i]
  | Void ->
      []
  | TerminalSpace p ->
      [p]
  | AbstractionSpace b ->
      extract tbl b |> List.map ~f:(fun b' -> Program.Abstraction b')
  | Universe ->
      [Primitive {ty= Id 0; name= "UNIVERSE"}]

(* unions are created when finding substitutions, after incorporating all
    frontier programs.  If extracting a program for a version space known
    to represent a frontier program (or part of one), extract should return
    exactly one program. *)
let extract_program tbl i =
  match extract tbl i with
  | [p] ->
      p
  | [] ->
      failwith
        "extract returned zero inhabitants for version space of frontier \
         program"
  | _ ->
      failwith
        "extract returned multiple inhabitants for version space of frontier \
         program (contains zero unions)"

let rec child_spaces tbl i =
  let children =
    match version_of_int tbl i with
    | Union u ->
        List.concat_map u ~f:(child_spaces tbl)
    | ApplySpace (f, x) ->
        child_spaces tbl f @ child_spaces tbl x
    | AbstractionSpace b ->
        child_spaces tbl b
    | _ ->
        []
  in
  List.dedup_and_sort (i :: children) ~compare:( - )

(* produces a version space equivalent to `i` with
     free variables downshifted by `n` *)
let rec downshift_free_vars ?(c = 0) tbl ~n ~i =
  if n = 0 then i
  else
    match version_of_int tbl i with
    | Union indices ->
        union tbl
        @@ List.map indices ~f:(fun j -> downshift_free_vars ~c tbl ~n ~i:j)
    | IndexSpace j when j < c ->
        i
    | IndexSpace j when j >= n + c ->
        version_of_index tbl (j - n)
    | IndexSpace _ ->
        tbl.void
    | ApplySpace (f, x) ->
        version_of_apply tbl
          (downshift_free_vars ~c tbl ~n ~i:f)
          (downshift_free_vars ~c tbl ~n ~i:x)
    | AbstractionSpace b ->
        version_of_abstraction tbl (downshift_free_vars ~c:(c + 1) tbl ~n ~i:b)
    | TerminalSpace _ | Universe | Void ->
        i

(* produces a version space equivalent to `i` with
    free variables upshifted by `n` *)
let rec upshift_free_vars ?(c = 0) tbl ~n ~i =
  if n = 0 then i
  else
    match version_of_int tbl i with
    | Union indices ->
        union tbl
        @@ List.map indices ~f:(fun j -> upshift_free_vars ~c tbl ~n ~i:j)
    | IndexSpace j when j < c ->
        i
    | IndexSpace j when j + n >= 0 ->
        version_of_index tbl (j + n)
    | IndexSpace _ ->
        tbl.void
    | ApplySpace (f, x) ->
        version_of_apply tbl
          (upshift_free_vars ~c tbl ~n ~i:f)
          (upshift_free_vars ~c tbl ~n ~i:x)
    | AbstractionSpace b ->
        version_of_abstraction tbl (upshift_free_vars ~c:(c + 1) tbl ~n ~i:b)
    | TerminalSpace _ | Universe | Void ->
        i

let rec subtract tbl a b =
  match (version_of_int tbl a, version_of_int tbl b) with
  | Universe, _ | _, Universe ->
      failwith "subtract: subtraction with universe is undefined"
  | Void, _ ->
      tbl.void
  | _, Void ->
      a
  | Union xs, _ ->
      union tbl @@ List.map xs ~f:(fun x -> subtract tbl x b)
  | _, Union xs ->
      List.fold xs ~init:a ~f:(fun acc remove -> subtract tbl acc remove)
  | AbstractionSpace b_a, AbstractionSpace b_b ->
      version_of_abstraction tbl (subtract tbl b_a b_b)
  | AbstractionSpace _, _ ->
      a
  | ApplySpace (f_a, x_a), ApplySpace (f_b, x_b) ->
      union tbl
        [ version_of_apply tbl (subtract tbl f_a f_b) x_a
        ; version_of_apply tbl f_a (subtract tbl x_a x_b) ]
  | ApplySpace _, _ ->
      a
  | IndexSpace i_a, IndexSpace i_b when i_a = i_b ->
      tbl.void
  | IndexSpace _, _ ->
      a
  | TerminalSpace t_a, TerminalSpace t_b when Program.equal t_a t_b ->
      tbl.void
  | TerminalSpace _, _ ->
      a

(* used to recursively eliminate redundancies in unions; has
    no effect on elements from a set of version spaces that
    contains no unions. *)
let rec unique_space tbl i =
  match version_of_int tbl i with
  | Universe | Void | IndexSpace _ | TerminalSpace _ ->
      i
  | AbstractionSpace b ->
      version_of_abstraction tbl (unique_space tbl b)
  | ApplySpace (f, x) ->
      version_of_apply tbl (unique_space tbl f) (unique_space tbl x)
  | Union u ->
      List.fold u ~init:tbl.void ~f:(fun uniques space ->
          union tbl [uniques; subtract tbl (unique_space tbl space) uniques] )

(* also trivial in the absence of unions*)
let rec intersection tbl a b =
  match (version_of_int tbl a, version_of_int tbl b) with
  | Universe, _ ->
      b
  | _, Universe ->
      a
  | Void, _ | _, Void ->
      tbl.void
  | Union xs, Union ys ->
      union tbl
      @@ List.concat_map xs ~f:(fun x ->
             List.map ys ~f:(fun y -> intersection tbl x y) )
  | Union xs, _ ->
      union tbl @@ List.map xs ~f:(fun x -> intersection tbl x b)
  | _, Union ys ->
      union tbl @@ List.map ys ~f:(fun y -> intersection tbl y a)
  | AbstractionSpace b_a, AbstractionSpace b_b ->
      version_of_abstraction tbl (intersection tbl b_a b_b)
  | ApplySpace (f_a, x_a), ApplySpace (f_b, x_b) ->
      version_of_apply tbl (intersection tbl f_a f_b) (intersection tbl x_a x_b)
  | IndexSpace i_a, IndexSpace i_b when i_a = i_b ->
      a
  | TerminalSpace p_a, TerminalSpace p_b when Program.equal p_a p_b ->
      a
  | _ ->
      tbl.void

let inline tbl =
  let rec go args i =
    match version_of_int tbl i with
    | Union u ->
        union tbl @@ List.map u ~f:(go args)
    | ApplySpace (f, x) ->
        go (x :: args) f
    | TerminalSpace (Invented {body; _}) ->
        let rec make_substitution env unused (b : Program.t) =
          match (unused, b) with
          | [], Abstraction _ ->
              None
          | [], _ ->
              Some (env, b)
          | x :: xs, Abstraction b' ->
              make_substitution (x :: env) xs b'
          | _ ->
              Some (env, b)
        in
        let rec apply_substitution ~k env : Program.t -> int = function
          | Index i when i < k ->
              version_of_index tbl i
          | Index i when i - k < List.length env ->
              upshift_free_vars tbl ~n:k ~i:(List.nth_exn env (i - k))
          | Index i ->
              version_of_index tbl (i - List.length env)
          | Apply (f, x) ->
              version_of_apply tbl
                (apply_substitution ~k env f)
                (apply_substitution ~k env x)
          | Abstraction b ->
              version_of_abstraction tbl (apply_substitution ~k:(k + 1) env b)
          | (Primitive _ | Invented _) as p ->
              incorporate tbl p
        in
        make_substitution [] args body
        |> Option.value_map ~default:tbl.void ~f:(fun (env, b) ->
               let f = apply_substitution ~k:0 env b in
               let unused = List.drop args @@ List.length env in
               List.fold unused ~init:f ~f:(version_of_apply tbl) )
    | Void | Universe | AbstractionSpace _ | IndexSpace _ | TerminalSpace _ ->
        tbl.void
  in
  go []

let rec inline_rec tbl i =
  match version_of_int tbl i with
  | Union u ->
      union tbl @@ List.map u ~f:(inline_rec tbl)
  | AbstractionSpace b ->
      version_of_abstraction tbl (inline_rec tbl b)
  | IndexSpace _ | Void | Universe | TerminalSpace (Primitive _) ->
      tbl.void
  | _ ->
      let top_inlinings = inline tbl i in
      let rec inline_args j =
        match version_of_int tbl j with
        | ApplySpace (f, x) ->
            version_of_apply tbl f (inline_rec tbl x)
        | Union u ->
            union tbl @@ List.map u ~f:inline_args
        | _ ->
            tbl.void
      in
      let arg_inlinings = inline_args i in
      union tbl [top_inlinings; arg_inlinings]

let rec intersecting ?(memo = None) tbl a b =
  if a = b then true
  else
    let a, b = if a > b then (b, a) else (a, b) in
    let go a b =
      match (version_of_int tbl a, version_of_int tbl b) with
      | Void, _ | _, Void ->
          false
      | Universe, _ | _, Universe ->
          true
      | Union xs, Union ys ->
          List.exists xs ~f:(fun x ->
              List.exists ys ~f:(fun y -> intersecting ~memo tbl x y) )
      | Union xs, _ ->
          List.exists xs ~f:(fun x -> intersecting ~memo tbl x b)
      | _, Union ys ->
          List.exists ys ~f:(fun y -> intersecting ~memo tbl y a)
      | AbstractionSpace b_a, AbstractionSpace b_b ->
          intersecting ~memo tbl b_a b_b
      | ApplySpace (f_a, x_a), ApplySpace (f_b, x_b) ->
          intersecting ~memo tbl f_a f_b && intersecting ~memo tbl x_a x_b
      | IndexSpace i_a, IndexSpace i_b ->
          i_a = i_b
      | TerminalSpace p_a, TerminalSpace p_b ->
          Program.equal p_a p_b
      | _ ->
          false
    in
    match memo with
    | Some memo -> (
      match Hashtbl.find memo (a, b) with
      | Some has_intersection ->
          has_intersection
      | None ->
          let has_intersection = go a b in
          Hashtbl.set memo ~key:(a, b) ~data:has_intersection ;
          has_intersection )
    | None ->
        go a b

let factored_substitution = ref false

let rec substitutions tbl ?(n = 0) i =
  match Hashtbl.find tbl.substitutions (i, n) with
  | Some m ->
      m
  | None ->
      let v = downshift_free_vars tbl ~n ~i in
      let m = Hashtbl.create (module Int) in
      ( if v <> tbl.void then
        let b = version_of_index tbl n in
        ignore (Hashtbl.add m ~key:v ~data:b : [`Duplicate | `Ok]) ) ;
      ( match version_of_int tbl i with
      | TerminalSpace _ ->
          ignore (Hashtbl.add m ~key:tbl.universe ~data:i : [`Duplicate | `Ok])
      | IndexSpace j ->
          let b = if j < n then i else version_of_index tbl (j + 1) in
          ignore (Hashtbl.add m ~key:tbl.universe ~data:b : [`Duplicate | `Ok])
      | AbstractionSpace b ->
          substitutions tbl ~n:(n + 1) b
          |> Hashtbl.iteri ~f:(fun ~key ~data ->
                 Hashtbl.add_exn m ~key ~data:(version_of_abstraction tbl data) )
      | Union u ->
          let new_m = Hashtbl.create (module Int) in
          List.iter u ~f:(fun x ->
              substitutions tbl ~n x
              |> Hashtbl.iteri ~f:(fun ~key:v ~data:b ->
                     match Hashtbl.find new_m v with
                     | Some bs ->
                         Hashtbl.set new_m ~key:v ~data:(b :: bs)
                     | None ->
                         Hashtbl.set new_m ~key:v ~data:[b] ) ) ;
          Hashtbl.iteri new_m ~f:(fun ~key ~data ->
              Hashtbl.set m ~key ~data:(union tbl data) )
      | ApplySpace (f, x) ->
          if !factored_substitution then (
            let new_m = Hashtbl.create (module Int) in
            let f_subs = substitutions tbl ~n f in
            let x_subs = substitutions tbl ~n x in
            Hashtbl.iteri f_subs ~f:(fun ~key:v_f ~data:b_f ->
                Hashtbl.iteri x_subs ~f:(fun ~key:v_x ~data:b_x ->
                    if intersecting tbl v_f v_x then
                      Hashtbl.update new_m (intersection tbl v_f v_x)
                        ~f:(function
                        | Some (bs_f, bs_x) ->
                            (b_f :: bs_f, b_x :: bs_x)
                        | None ->
                            ([b_f], [b_x]) ) ) ) ;
            Hashtbl.iteri new_m ~f:(fun ~key ~data:(bs_f, bs_x) ->
                Hashtbl.set m ~key
                  ~data:(version_of_apply tbl (union tbl bs_f) (union tbl bs_x)) )
            )
          else
            let new_m = Hashtbl.create (module Int) in
            let f_subs = substitutions tbl ~n f in
            let x_subs = substitutions tbl ~n x in
            Hashtbl.iteri f_subs ~f:(fun ~key:v_f ~data:b_f ->
                Hashtbl.iteri x_subs ~f:(fun ~key:v_x ~data:b_x ->
                    if intersecting tbl v_f v_x then
                      let v = intersection tbl v_f v_x in
                      let app = version_of_apply tbl b_f b_x in
                      match Hashtbl.find new_m v with
                      | Some apps ->
                          Hashtbl.set new_m ~key:v ~data:(app :: apps)
                      | None ->
                          Hashtbl.set new_m ~key:v ~data:[app] ) ) ;
            Hashtbl.iteri new_m ~f:(fun ~key ~data ->
                Hashtbl.set m ~key ~data:(union tbl data) )
      | _ ->
          () ) ;
      Hashtbl.set tbl.substitutions ~key:(i, n) ~data:m ;
      m

let not_trivial_inversion tbl (v, b) =
  if
    v = tbl.universe || Version_space.equal (version_of_int tbl b) (IndexSpace 0)
  then None
  else Some (version_of_apply tbl (version_of_abstraction tbl b) v)

let inversion tbl i =
  union tbl
  @@ List.filter_map ~f:(not_trivial_inversion tbl)
  @@ Hashtbl.to_alist @@ substitutions tbl i

let rec inversion_rec tbl i =
  match Array_list.get tbl.inversions i with
  | Some invs ->
      invs
  | None ->
      let invs =
        match version_of_int tbl i with
        | Union u ->
            union tbl @@ List.map u ~f:(inversion_rec tbl)
        | _ ->
            let top_invs =
              List.filter_map ~f:(not_trivial_inversion tbl)
              @@ Hashtbl.to_alist @@ substitutions tbl i
            in
            let child_invs =
              match version_of_int tbl i with
              | ApplySpace (f, x) ->
                  [ version_of_apply tbl (inversion_rec tbl f) x
                  ; version_of_apply tbl f (inversion_rec tbl x) ]
              | AbstractionSpace b ->
                  [version_of_abstraction tbl (inversion_rec tbl b)]
              | _ ->
                  []
            in
            union tbl (child_invs @ top_invs)
      in
      Array_list.set tbl.inversions i (Some invs) ;
      invs

(* Strips a version space of all inhabitant programs containing an applied lambda
    as the function of another applied lambda.  Returns the alternative version
    space. Used to ensure that applications are floated outside of all abstractions
    in an expression. *)
let rec beta_pruning ?(is_applied = false) ?(can_beta = true) tbl i =
  match version_of_int tbl i with
  | ApplySpace (f, x) ->
      let f' = beta_pruning ~is_applied:true ~can_beta tbl f in
      let x' = beta_pruning ~is_applied:false ~can_beta tbl x in
      version_of_apply tbl f' x'
  | AbstractionSpace b ->
      if not is_applied then
        let b' = beta_pruning ~is_applied ~can_beta tbl b in
        version_of_abstraction tbl b'
      else if not can_beta then tbl.void
      else
        let b' = beta_pruning ~is_applied:false ~can_beta:false tbl b in
        version_of_abstraction tbl b'
  | Union u ->
      union tbl @@ List.map u ~f:(beta_pruning ~is_applied ~can_beta tbl)
  | IndexSpace _ | TerminalSpace _ | Universe | Void ->
      i

let rec log_version_size tbl i =
  match version_of_int tbl i with
  | ApplySpace (f, x) ->
      log_version_size tbl f +. log_version_size tbl x
  | AbstractionSpace b ->
      log_version_size tbl b
  | Union us ->
      log (List.reduce_exn ~f:( +. ) @@ List.map us ~f:(log_version_size tbl))
  | _ ->
      0.

let n_step_inversion ?(inlining = false) tbl ~n i =
  let key = (n, i) in
  match Hashtbl.find tbl.n_step key with
  | Some ns ->
      ns
  | None ->
      let step v =
        if inlining then union tbl [inversion_rec tbl v; inline tbl v]
        else inversion_rec tbl v
      in
      let rec n_step ?(k = 0) k_step =
        let rest = if k < n then n_step ~k:(k + 1) (step k_step) else [] in
        beta_pruning tbl k_step :: rest
      in
      let rec add_children j =
        let children =
          match version_of_int tbl j with
          | Union _ | Void | Universe ->
              failwith "n_step_inversion: add_children"
          | ApplySpace (f, x) ->
              version_of_apply tbl (add_children f) (add_children x)
          | AbstractionSpace b ->
              version_of_abstraction tbl (add_children b)
          | IndexSpace _ | TerminalSpace _ ->
              j
        in
        union tbl (children :: n_step j)
      in
      let ns = beta_pruning tbl @@ add_children i in
      Hashtbl.set tbl.n_step ~key ~data:ns ;
      ns

let reachable_versions tbl is =
  let visited = Hash_set.Poly.create () in
  let rec go i =
    if not (Hash_set.mem visited i) then (
      Hash_set.add visited i ;
      match version_of_int tbl i with
      | AbstractionSpace b ->
          go b
      | ApplySpace (f, x) ->
          go f ; go x
      | Union u ->
          List.iter u ~f:go
      | _ ->
          () )
  in
  List.iter is ~f:go ; Hash_set.to_list visited

let gc_versions ?(verbose = false) tbl is =
  let tbl' = create () in
  let rec transfer i =
    match version_of_int tbl i with
    | Union u ->
        union tbl' @@ List.map u ~f:transfer
    | ApplySpace (f, x) ->
        version_of_apply tbl' (transfer f) (transfer x)
    | AbstractionSpace b ->
        version_of_abstraction tbl' (transfer b)
    | IndexSpace i ->
        version_of_index tbl' i
    | TerminalSpace p ->
        version_of_terminal tbl' p
    | Universe ->
        tbl'.universe
    | Void ->
        tbl'.void
  in
  let is = List.map is ~f:(List.map ~f:transfer) in
  if verbose then (
    Printf.eprintf "GC reduced table to %d%% of previous size\n"
      (100 * (tbl'.int2space.occupancy / tbl.int2space.occupancy)) ;
    Util.flush_all () ) ;
  (tbl', is)

let epsilon_cost = 0.01
