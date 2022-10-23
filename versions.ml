open Core
open Program
open Type
module Array_list = Util.Array_list

type version_space =
  | Union of int list
  | ApplySpace of int * int
  | AbstractionSpace of int
  | IndexSpace of int
  | TerminalSpace of program
  | Universe
  | Void
[@@deriving equal, compare, sexp_of, hash]

module VersionSpace = struct
  type t = version_space [@@deriving compare, sexp_of, hash]
end

type version_tbl =
  { universe: int
  ; void: int
  ; space2int: (version_space, int) Hashtbl.t
  ; int2space: version_space Array_list.t
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
      string_of_program p
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

let new_version_tbl () =
  let tbl =
    { void= 0
    ; universe= 1
    ; space2int= Hashtbl.create (module VersionSpace)
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

let rec incorporate tbl = function
  | Index i ->
      version_of_index tbl i
  | Abstraction b ->
      version_of_abstraction tbl @@ incorporate tbl b
  | Apply (f, x) ->
      version_of_apply tbl (incorporate tbl f) (incorporate tbl x)
  | (Primitive _ | Invented _) as p ->
      version_of_terminal tbl p

let rec extract tbl i =
  match version_of_int tbl i with
  | Union u ->
      List.concat_map u ~f:(extract tbl)
  | ApplySpace (f, x) ->
      extract tbl f
      |> List.concat_map ~f:(fun f' ->
             extract tbl x |> List.map ~f:(fun x' -> Apply (f', x')) )
  | IndexSpace i ->
      [Index i]
  | Void ->
      []
  | TerminalSpace p ->
      [p]
  | AbstractionSpace b ->
      extract tbl b |> List.map ~f:(fun b' -> Abstraction b')
  | Universe ->
      [Primitive {ty= Id 0; name= "UNIVERSE"}]

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

let rec shift_free ?(c = 0) tbl ~n ~i =
  if n = 0 then i
  else
    match version_of_int tbl i with
    | Union indices ->
        union tbl @@ List.map indices ~f:(fun j -> shift_free ~c tbl ~n ~i:j)
    | IndexSpace j when j < c ->
        i
    | IndexSpace j when j >= n + c ->
        version_of_index tbl (j - n)
    | IndexSpace _ ->
        tbl.void
    | ApplySpace (f, x) ->
        version_of_apply tbl
          (shift_free ~c tbl ~n ~i:f)
          (shift_free ~c tbl ~n ~i:x)
    | AbstractionSpace b ->
        version_of_abstraction tbl (shift_free ~c:(c + 1) tbl ~n ~i:b)
    | TerminalSpace _ | Universe | Void ->
        i

let rec shift_versions ?(c = 0) tbl ~n ~i =
  if n = 0 then i
  else
    match version_of_int tbl i with
    | Union indices ->
        union tbl
        @@ List.map indices ~f:(fun j -> shift_versions ~c tbl ~n ~i:j)
    | IndexSpace j when j < c ->
        i
    | IndexSpace j when j + n >= 0 ->
        version_of_index tbl (j + n)
    | IndexSpace _ ->
        tbl.void
    | ApplySpace (f, x) ->
        version_of_apply tbl
          (shift_versions ~c tbl ~n ~i:f)
          (shift_versions ~c tbl ~n ~i:x)
    | AbstractionSpace b ->
        version_of_abstraction tbl (shift_versions ~c:(c + 1) tbl ~n ~i:b)
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
  | TerminalSpace t_a, TerminalSpace t_b when equal_program t_a t_b ->
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
  | TerminalSpace p_a, TerminalSpace p_b when equal_program p_a p_b ->
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
    | TerminalSpace (Invented (_, b)) ->
        let rec make_substitution env unused b =
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
        let rec apply_substitution ~k env = function
          | Index i when i < k ->
              version_of_index tbl i
          | Index i when i - k < List.length env ->
              shift_versions tbl ~n:k ~i:(List.nth_exn env (i - k))
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
        make_substitution [] args b
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
          equal_program p_a p_b
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
      let v = shift_free tbl ~n ~i in
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
    v = tbl.universe || equal_version_space (version_of_int tbl b) (IndexSpace 0)
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
  let tbl' = new_version_tbl () in
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

type cost_tbl =
  { function_cost: (float * int list) option Array_list.t
  ; argument_cost: (float * int list) option Array_list.t
  ; parent: version_tbl }

let empty_cost_tbl tbl =
  { function_cost= Array_list.create ()
  ; argument_cost= Array_list.create ()
  ; parent= tbl }

(* The minimal inhabitants-related functions all abbreviate
    their search by skipping inhabitants containing applications
    whose functions are abstractions.  This is justified by the
    fact that any application whose function is a abstraction is
    unnecessary (one could find the inhabitant with this application
    already beta-reduced).  I assume this trick saves on performance,
    because strictly speaking it should not be necessary for the
    correctness of the implementation. *)
let rec minimum_cost_inhabitants ?(given = None) ?(can_be_lambda = true)
    cost_tbl i =
  let cache =
    if can_be_lambda then cost_tbl.argument_cost else cost_tbl.function_cost
  in
  Array_list.ensure_length cache (i + 1) None ;
  match Array_list.get cache i with
  | Some c_inds ->
      c_inds
  | None ->
      let c, inds =
        match given with
        | Some invention when intersecting cost_tbl.parent invention i ->
            (1., [invention])
        | _ -> (
          match version_of_int cost_tbl.parent i with
          | Universe | Void ->
              failwith "minimum_cost_inhabitants"
          | IndexSpace _ | TerminalSpace _ ->
              (1., [i])
          | Union u ->
              let children =
                List.map u
                  ~f:(minimum_cost_inhabitants ~given ~can_be_lambda cost_tbl)
              in
              let c = Util.fold1 Float.min @@ List.map children ~f:fst in
              if Util.is_invalid c then (c, [])
              else
                let children =
                  List.concat_map ~f:snd
                  @@ List.filter children ~f:(fun (cost, _) ->
                         Float.(cost = c) )
                in
                (c, children)
          | AbstractionSpace b when can_be_lambda ->
              let c, children =
                minimum_cost_inhabitants ~given ~can_be_lambda cost_tbl b
              in
              let c = c +. epsilon_cost in
              let children =
                List.map children ~f:(version_of_abstraction cost_tbl.parent)
              in
              (c, children)
          | AbstractionSpace _ ->
              (Float.infinity, [])
          | ApplySpace (f, x) ->
              let c_f, children_f =
                minimum_cost_inhabitants ~given ~can_be_lambda:false cost_tbl f
              in
              let c_x, children_x =
                minimum_cost_inhabitants ~given ~can_be_lambda:true cost_tbl x
              in
              if Util.is_invalid c_f || Util.is_invalid c_x then
                (Float.infinity, [])
              else
                ( c_f +. c_x +. epsilon_cost
                , List.concat_map children_f ~f:(fun f' ->
                      List.map children_x ~f:(fun x' ->
                          version_of_apply cost_tbl.parent f' x' ) ) ) )
      in
      let c_inds = (c, List.dedup_and_sort inds ~compare:( - )) in
      Array_list.set cache i (Some c_inds) ;
      c_inds

type 'a cheap_cost_tbl =
  { function_cost: float option Array_list.t
  ; argument_cost: float option Array_list.t
  ; parent: version_tbl }

let empty_cheap_cost_tbl tbl =
  { function_cost= Array_list.create ()
  ; argument_cost= Array_list.create ()
  ; parent= tbl }

let rec minimal_inhabitant_cost ?(memo = None) ?(given = None)
    ?(can_be_lambda = true) cost_tbl i =
  let cache =
    if can_be_lambda then cost_tbl.argument_cost else cost_tbl.function_cost
  in
  Array_list.ensure_length cache (i + 1) None ;
  match Array_list.get cache i with
  | Some c_inds ->
      c_inds
  | None ->
      let c =
        match given with
        | Some invention when intersecting ~memo cost_tbl.parent invention i ->
            1.
        | _ -> (
          match version_of_int cost_tbl.parent i with
          | Universe | Void ->
              failwith "minimal_inhabitant_cost"
          | IndexSpace _ | TerminalSpace _ ->
              1.
          | Union u ->
              Util.fold1 Float.min
              @@ List.map u
                   ~f:
                     (minimal_inhabitant_cost ~memo ~given ~can_be_lambda
                        cost_tbl )
          | AbstractionSpace b when can_be_lambda ->
              epsilon_cost
              +. minimal_inhabitant_cost ~memo ~given ~can_be_lambda cost_tbl b
          | AbstractionSpace _ ->
              Float.infinity
          | ApplySpace (f, x) ->
              epsilon_cost
              +. minimal_inhabitant_cost ~memo ~given ~can_be_lambda:false
                   cost_tbl f
              +. minimal_inhabitant_cost ~memo ~given ~can_be_lambda:true
                   cost_tbl x )
      in
      Array_list.set cache i (Some c) ;
      c

let rec minimal_inhabitant ?(memo = None) ?(given = None)
    ?(can_be_lambda = true) cost_tbl i =
  let c = minimal_inhabitant_cost ~memo ~given ~can_be_lambda cost_tbl i in
  if Util.is_invalid c then None
  else
    let p =
      match (c, given) with
      | 1., Some invention when intersecting ~memo cost_tbl.parent invention i
        ->
          Util.singleton_list @@ extract cost_tbl.parent invention
      | _ -> (
        match version_of_int cost_tbl.parent i with
        | Universe | Void ->
            failwith "minimal_inhabitant"
        | IndexSpace _ | TerminalSpace _ ->
            Util.singleton_list @@ extract cost_tbl.parent i
        | Union u ->
            Util.value_exn
            @@ minimal_inhabitant ~memo ~given ~can_be_lambda cost_tbl
            @@ Util.minimum_by u ~compare:Float.compare
                 ~f:
                   (minimal_inhabitant_cost ~memo ~given ~can_be_lambda cost_tbl)
        | AbstractionSpace b ->
            Abstraction
              ( Util.value_exn
              @@ minimal_inhabitant ~memo ~given ~can_be_lambda:true cost_tbl b
              )
        | ApplySpace (f, x) ->
            Apply
              ( Util.value_exn
                @@ minimal_inhabitant ~memo ~given ~can_be_lambda:false cost_tbl
                     f
              , Util.value_exn
                @@ minimal_inhabitant ~memo ~given ~can_be_lambda:true cost_tbl
                     x ) )
    in
    Some p

type beam =
  { unrefactored_func_cost: float
  ; unrefactored_arg_cost: float
  ; mutable refactored_func_cost: (int, float) Hashtbl.t
  ; mutable refactored_arg_cost: (int, float) Hashtbl.t }

let limit_beam ~beam_size b =
  let limit beam =
    if Hashtbl.length beam > beam_size then
      Hashtbl.to_alist beam
      |> List.sort ~compare:(fun (_, c_1) (_, c_2) -> Float.compare c_1 c_2)
      |> (Fn.flip List.take) beam_size
      |> Hashtbl.of_alist_exn (module Int)
    else beam
  in
  b.refactored_func_cost <- limit b.refactored_func_cost ;
  b.refactored_arg_cost <- limit b.refactored_arg_cost

let relax tbl ~key ~data =
  Hashtbl.change tbl key
    ~f:
      (Option.value_map ~default:(Some data) ~f:(fun v ->
           if Float.(v > data) then Some data else None ) )

let func_cost b i =
  Hashtbl.find b.refactored_func_cost i
  |> Option.value_map ~f:Fn.id ~default:b.unrefactored_func_cost

let arg_cost b i =
  Hashtbl.find b.refactored_arg_cost i
  |> Option.value_map ~f:Fn.id ~default:b.unrefactored_arg_cost

let refactorings_costs tbl refactorings =
  let costs = Hashtbl.create (module Int) in
  List.iter refactorings ~f:(fun refactoring ->
      let cost =
        Float.of_int @@ List.length
        @@ List.dedup_and_sort ~compare:( - )
        @@ free_variables @@ Util.singleton_list @@ extract tbl refactoring
      in
      Hashtbl.set costs ~key:refactoring ~data:(1. +. cost) ) ;
  costs

let beams ~(cost_tbl : cost_tbl) ~beam_size refactorings transforms =
  let costs = refactorings_costs cost_tbl.parent refactorings in
  let refactorings = Hash_set.Poly.of_list refactorings in
  let cache = Array_list.create () in
  let rec go i =
    Array_list.ensure_length cache (i + 1) None ;
    match Array_list.get cache i with
    | Some beam ->
        beam
    | None ->
        let unrefactored_arg_cost, inhabitants =
          minimum_cost_inhabitants ~can_be_lambda:true cost_tbl i
        in
        let unrefactored_func_cost, _ =
          minimum_cost_inhabitants ~can_be_lambda:false cost_tbl i
        in
        let beam =
          { unrefactored_arg_cost
          ; unrefactored_func_cost
          ; refactored_func_cost= Hashtbl.create (module Int)
          ; refactored_arg_cost= Hashtbl.create (module Int) }
        in
        List.filter inhabitants ~f:(Hash_set.mem refactorings)
        |> List.iter ~f:(fun refactoring ->
               let cost = Hashtbl.find_exn costs refactoring in
               Hashtbl.set beam.refactored_func_cost ~key:refactoring ~data:cost ;
               Hashtbl.set beam.refactored_arg_cost ~key:refactoring ~data:cost ) ;
        ( match version_of_int cost_tbl.parent i with
        | AbstractionSpace b ->
            let child = go b in
            Hashtbl.iteri child.refactored_arg_cost ~f:(fun ~key ~data ->
                relax beam.refactored_arg_cost ~key ~data:(data +. epsilon_cost) )
        | ApplySpace (f, x) ->
            let beam_f = go f in
            let beam_x = go x in
            let refactored_with =
              Hashtbl.keys beam_f.refactored_func_cost
              @ Hashtbl.keys beam_x.refactored_arg_cost
            in
            List.iter refactored_with ~f:(fun refactoring ->
                let c =
                  epsilon_cost
                  +. func_cost beam_f refactoring
                  +. arg_cost beam_x refactoring
                in
                relax beam.refactored_func_cost ~key:refactoring ~data:c ;
                relax beam.refactored_arg_cost ~key:refactoring ~data:c )
        | Union u ->
            List.iter u ~f:(fun v ->
                let child = go v in
                Hashtbl.iteri child.refactored_func_cost ~f:(fun ~key ~data ->
                    relax beam.refactored_func_cost ~key ~data ) ;
                Hashtbl.iteri child.refactored_arg_cost ~f:(fun ~key ~data ->
                    relax beam.refactored_arg_cost ~key ~data ) )
        | IndexSpace _ | Universe | Void | TerminalSpace _ ->
            () ) ;
        limit_beam ~beam_size beam ;
        Array_list.set cache i (Some beam) ;
        beam
  in
  List.iter transforms ~f:(fun i -> ignore (go i : beam)) ;
  cache

let beam_costs ~cost_tbl ~beam_size refactorings transforms =
  let cache = beams ~cost_tbl ~beam_size refactorings transforms in
  let beams =
    List.map transforms ~f:(fun i -> Util.value_exn @@ Array_list.get cache i)
  in
  List.map refactorings ~f:(fun refactoring ->
      Util.fold1 ( +. )
      @@ List.map beams ~f:(fun beam ->
             Float.min (arg_cost beam refactoring) (func_cost beam refactoring) ) )

let beams_and_costs ~cost_tbl ~beam_size refactorings transforms =
  let costs = beam_costs ~cost_tbl ~beam_size refactorings transforms in
  List.zip_exn costs refactorings
  |> List.sort ~compare:(fun (s_1, _) (s_2, _) -> Float.compare s_1 s_2)
