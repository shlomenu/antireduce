open Core

type cons_signature = {name: string; parameters: dc_type list; polymorphic: bool}
[@@deriving compare, hash, sexp_of, yojson]

and arrow_signature = {left: dc_type; right: dc_type; polymorphic: bool}
[@@deriving compare, hash, sexp_of, yojson]

and dc_type =
  | Id of int
  | Constructor of cons_signature
  | Arrow of arrow_signature
[@@deriving compare, hash, sexp_of, yojson]

let is_polymorphic = function
  | Id _ ->
      true
  | Constructor {polymorphic; _} | Arrow {polymorphic; _} ->
      polymorphic

let rec equal_dc_type ty_a ty_b =
  match (ty_a, ty_b) with
  | Id id_a, Id id_b ->
      id_a = id_b
  | Constructor con_a, Constructor con_b ->
      String.(con_a.name = con_b.name)
      && List.equal equal_dc_type con_a.parameters con_b.parameters
  | Arrow arw_a, Arrow arw_b ->
      equal_dc_type arw_a.left arw_b.left
      && equal_dc_type arw_a.right arw_b.right
  | _ ->
      false

module DcType = struct
  type t = dc_type [@@deriving equal, compare, sexp_of]

  include Comparator.Make (struct
    type t = dc_type [@@deriving equal, compare, sexp_of]
  end)
end

let kind name parameters =
  let polymorphic = List.exists parameters ~f:is_polymorphic in
  Constructor {name; parameters; polymorphic}

type type_context =
  {next_id: int; types: (Int.t, dc_type, Int.comparator_witness) Map.t}

let empty_type_context = {next_id= 0; types= Map.empty (module Int)}

let arrow left right =
  let polymorphic = is_polymorphic left || is_polymorphic right in
  Arrow {left; right; polymorphic}

let ( @> ) = arrow

let is_arrow = function Arrow _ -> true | _ -> false

let rec list_of_arrows = function
  | Arrow {left; right; _} ->
      left :: list_of_arrows right
  | ty ->
      [ty]

let rec arrows_of_list = function
  | [last] ->
      last
  | left :: right ->
      arrow left @@ arrows_of_list right
  | [] ->
      failwith "arrows_of_list: cannot create type from empty list"

let rec parameters_and_terminal_of_type = function
  | Arrow {left; right; _} ->
      let parameters, terminal = parameters_and_terminal_of_type right in
      (left :: parameters, terminal)
  | ty ->
      ([], ty)

let rec terminal_of_type = function
  | Arrow {right; _} ->
      terminal_of_type right
  | ty ->
      ty

let rec parameters_of_type = function
  | Arrow {left; right; _} ->
      left :: parameters_of_type right
  | _ ->
      []

let right_of_arrow = function
  | Arrow {right; _} ->
      right
  | _ ->
      failwith "right_of_arrow: not an arrow"

let left_of_arrow = function
  | Arrow {left; _} ->
      left
  | _ ->
      failwith "left_of_arrow: not a constructor"

let string_of_dc_type : dc_type -> string =
  let rec go parenthesized = function
    | Id i ->
        "t" ^ string_of_int i
    | Arrow {left; right; _} ->
        let body = go true left ^ " -> " ^ go false right in
        if parenthesized then "(" ^ body ^ ")" else body
    | Constructor {name; parameters; _} ->
        if List.is_empty parameters then name
        else
          let params =
            List.map parameters ~f:(go false) |> String.concat ~sep:", "
          in
          name ^ "(" ^ params ^ ")"
  in
  go false

let make_type_id ({next_id; types} as cxt) =
  assert (Option.is_none @@ Map.find types next_id) ;
  (Id next_id, {cxt with next_id= next_id + 1})

let rec make_type_ids (n : int) ?(ids = []) (cxt : type_context) :
    dc_type list * type_context =
  if n <= 0 then (List.rev ids, cxt)
  else
    let ty, cxt = make_type_id cxt in
    let ids = ty :: ids in
    make_type_ids (n - 1) ~ids cxt

let bind_type_id i ty cxt : type_context =
  {cxt with types= Map.set cxt.types ~key:i ~data:ty}

let lookup_type_id cxt i =
  assert (i < cxt.next_id) ;
  Map.find cxt.types i

let rec apply_context cxt = function
  | ty when not (is_polymorphic ty) ->
      (cxt, ty)
  | Id j as ty -> (
    match lookup_type_id cxt j with
    | Some ty_other ->
        let cxt, ty' = apply_context cxt ty_other in
        let cxt =
          if equal_dc_type ty ty' then cxt else bind_type_id j ty' cxt
        in
        (cxt, ty')
    | None ->
        (cxt, ty) )
  | Constructor con ->
      let f parameter (cxt, parameters) =
        let cxt, parameter = apply_context cxt parameter in
        (cxt, parameter :: parameters)
      in
      let cxt, parameters = List.fold_right con.parameters ~init:(cxt, []) ~f in
      (cxt, kind con.name parameters)
  | Arrow {left; right; _} ->
      let cxt, right = apply_context cxt right in
      let cxt, left = apply_context cxt left in
      (cxt, arrow left right)

let compose_substitutions cxt_a cxt_b =
  let next_id = max cxt_a.next_id cxt_b.next_id in
  let types =
    List.range ~start:`inclusive ~stop:`exclusive 0 (next_id - 1)
    |> List.filter_map ~f:(fun i ->
           let ty = Id i in
           let ty =
             if i < cxt_a.next_id then snd @@ apply_context cxt_a ty else ty
           in
           let ty =
             if i < cxt_b.next_id then snd @@ apply_context cxt_b ty else ty
           in
           if equal_dc_type ty (Id i) then None else Some (i, ty) )
    |> Map.of_alist_exn (module Int)
  in
  {next_id; types}

let rec occurs i = function
  | ty when not (is_polymorphic ty) ->
      false
  | Arrow {left; right; _} ->
      occurs i left || occurs i right
  | Constructor {parameters; _} ->
      List.exists parameters ~f:(occurs i)
  | Id j ->
      j = i

let occurs_check = true

exception UnificationFailure of string

let rec might_unify ty_1 ty_2 =
  match (ty_1, ty_2) with
  | Constructor con_1, Constructor con_2 when String.(con_1.name = con_2.name)
    ->
      List.for_all2_exn con_1.parameters con_2.parameters ~f:might_unify
  | Arrow arw_1, Arrow arw_2 ->
      might_unify arw_1.left arw_2.left && might_unify arw_1.right arw_2.right
  | Id _, _ | _, Id _ ->
      true
  | _ ->
      false

let rec unify cxt ty_1 ty_2 =
  let cxt, ty_1 = apply_context cxt ty_1 in
  let cxt, ty_2 = apply_context cxt ty_2 in
  if (not (is_polymorphic ty_1)) && not (is_polymorphic ty_2) then
    if equal_dc_type ty_1 ty_2 then cxt
    else
      raise
        (UnificationFailure
           (Format.sprintf "monomorphic types are not equal: %s <> %s"
              (string_of_dc_type ty_1) (string_of_dc_type ty_2) ) )
  else
    match (ty_1, ty_2) with
    | Id j, ty_other | ty_other, Id j ->
        if equal_dc_type ty_1 ty_2 then cxt
        else if occurs j ty_other then
          raise
            (UnificationFailure
               (Format.sprintf "occurs check did not pass: %s occurs in %s"
                  (string_of_dc_type (Id j))
                  (string_of_dc_type ty_other) ) )
        else bind_type_id j ty_other cxt
    | Arrow arw_1, Arrow arw_2 ->
        let cxt = unify cxt arw_1.left arw_2.left in
        unify cxt arw_1.right arw_2.right
    | Constructor con_1, Constructor con_2 when String.(con_1.name = con_2.name)
      ->
        List.fold2_exn ~init:cxt con_1.parameters con_2.parameters ~f:unify
    | _ ->
        raise
          (UnificationFailure
             (Format.sprintf "dissimilar structure: %s <> %s"
                (string_of_dc_type ty_1) (string_of_dc_type ty_2) ) )

let instantiate_type cxt ty =
  let types = ref [] in
  let cxt_ref = ref cxt in
  let rec instantiate = function
    | ty_j when not (is_polymorphic ty_j) ->
        ty_j
    | Id i -> (
      try List.Assoc.find_exn ~equal !types i
      with Not_found_s _ ->
        let ty, cxt' = make_type_id !cxt_ref in
        cxt_ref := cxt' ;
        types := (i, ty) :: !types ;
        ty )
    | Arrow {left; right; _} ->
        arrow (instantiate left) (instantiate right)
    | Constructor {name; parameters; _} ->
        kind name @@ List.map parameters ~f:instantiate
  in
  let ty_inst = instantiate ty in
  (!cxt_ref, ty_inst)

let canonical_type ?next_id_ref ?types ty =
  let next_id_ref = match next_id_ref with Some r -> r | None -> ref 0 in
  let types = match types with Some types -> types | None -> ref [] in
  let rec go = function
    | Id i -> (
      try Id (List.Assoc.find_exn ~equal !types i)
      with Not_found_s _ ->
        let canonical_id = !next_id_ref in
        types := (i, canonical_id) :: !types ;
        next_id_ref := canonical_id + 1 ;
        Id canonical_id )
    | (Arrow {polymorphic= false; _} | Constructor {polymorphic= false; _}) as
      ty ->
        ty
    | Arrow {left; right; _} ->
        arrow (go left) (go right)
    | Constructor {name; parameters; _} ->
        kind name @@ List.map parameters ~f:go
  in
  go ty

let rec next_type_var = function
  | Id i ->
      i + 1
  | Arrow {polymorphic= false; _}
  | Constructor {polymorphic= false; _}
  | Constructor {parameters= []; _} ->
      0
  | Arrow {left; right; _} ->
      max (next_type_var left) (next_type_var right)
  | Constructor {parameters; _} ->
      List.map parameters ~f:next_type_var |> List.fold ~init:0 ~f:max

let next_type_vars tys =
  List.fold ~init:0 ~f:max @@ List.map tys ~f:next_type_var

let rec increment_type_variables c = function
  | Arrow arw as ty ->
      if arw.polymorphic then
        let left = increment_type_variables c arw.left in
        let right = increment_type_variables c arw.right in
        Arrow {arw with left; right}
      else ty
  | Constructor con as ty ->
      if con.polymorphic then
        let parameters =
          List.map con.parameters ~f:(increment_type_variables c)
        in
        Constructor {con with parameters}
      else ty
  | Id n ->
      Id (n + c)

let apply_context_ref cxt_ref ty =
  let cxt', ty' = apply_context !cxt_ref ty in
  cxt_ref := cxt' ;
  ty'

let unify_ref cxt_ref ty_1 ty_2 = cxt_ref := unify !cxt_ref ty_1 ty_2

let instantiate_type_ref cxt_ref ty =
  let cxt', ty' = instantiate_type !cxt_ref ty in
  cxt_ref := cxt' ;
  ty'

let canonical_types tys =
  let next_id_ref = ref 0 in
  let types = ref [] in
  let f = canonical_type ~next_id_ref ~types in
  List.map tys ~f

let rec arity = function Arrow {right; _} -> 1 + arity right | _ -> 0

let rec pad_type cxt n ty =
  if n <= 0 then (cxt, ty)
  else
    let p, cxt = make_type_id cxt in
    let cxt, ps = pad_type cxt (n - 1) ty in
    (cxt, p @> ps)

let ground name = Constructor {name; parameters= []; polymorphic= false}

let unify_many_types tys =
  let ty, cxt = make_type_id empty_type_context in
  let cxt_ref = ref cxt in
  List.iter tys ~f:(fun ty' ->
      let cxt', ty' = instantiate_type !cxt_ref ty' in
      cxt_ref := unify cxt' ty' ty ) ;
  snd @@ apply_context !cxt_ref ty

type fast_cons_signature =
  {name: string; parameters: fast_type list; polymorphic: dc_type option}

and fast_arrow_signature =
  {left: fast_type; right: fast_type; polymorphic: dc_type option}

and fast_type =
  | FId of dc_type option ref
  | FArrow of fast_arrow_signature
  | FConstructor of fast_cons_signature

let rec aligned fast_ty ty =
  match (fast_ty, ty) with
  | FArrow {right= fast_right; _}, Arrow {right; _} ->
      aligned fast_right right
  | _, Id _ | FId _, _ | FConstructor _, Constructor _ ->
      true
  | FArrow _, Constructor _ | FConstructor _, Arrow _ ->
      false

let rec align_rev ?(parameters = []) fast_ty ty =
  if aligned fast_ty ty then Some (parameters, fast_ty)
  else
    match (fast_ty, ty) with
    | FArrow {left= fast_left; right= fast_right; _}, Arrow {right; _} ->
        align_rev ~parameters:(fast_left :: parameters) fast_right right
    | _ ->
        None

let align fast_ty req =
  align_rev fast_ty req
  |> Option.map ~f:(fun (parameters_rev, suffix) ->
         (List.rev parameters_rev, suffix) )

let fast_of_slow ty =
  let ty = canonical_type ty in
  let next_id = next_type_var ty in
  let types = Array.init next_id ~f:(fun _ -> ref None) in
  let rec go = function
    | Id i ->
        FId (Array.get types i)
    | Arrow a as ty ->
        FArrow
          { left= go a.left
          ; right= go a.right
          ; polymorphic= (if a.polymorphic then None else Some ty) }
    | Constructor c as ty ->
        FConstructor
          { name= c.name
          ; parameters= List.map c.parameters ~f:go
          ; polymorphic= (if c.polymorphic then None else Some ty) }
  in
  (go ty, types)

let rec slow_of_fast next_id_ref = function
  | FArrow a ->
      arrow (slow_of_fast next_id_ref a.left) (slow_of_fast next_id_ref a.right)
  | FConstructor con ->
      kind con.name @@ List.map con.parameters ~f:(slow_of_fast next_id_ref)
  | FId ({contents= ty_opt} as ty_opt_ref) -> (
    match ty_opt with
    | Some ty ->
        ty
    | None ->
        let ty = Id !next_id_ref in
        incr next_id_ref ;
        ty_opt_ref := Some ty ;
        ty )

let rec fast_unify cxt fast_ty ty =
  match (fast_ty, ty) with
  | FId ({contents= ty_opt} as ty_opt_ref), ty -> (
    match ty_opt with
    | Some ty' ->
        unify cxt ty' ty
    | None ->
        ty_opt_ref := Some ty ;
        cxt )
  | FArrow f_a, Arrow a ->
      let cxt = fast_unify cxt f_a.left a.left in
      fast_unify cxt f_a.right a.right
  | FConstructor f_c, Constructor c ->
      if String.(f_c.name = c.name) then
        List.fold2_exn f_c.parameters c.parameters ~init:cxt ~f:fast_unify
      else
        raise
          (UnificationFailure
             (Format.sprintf "constructors are not the same: %s <> %s" f_c.name
                c.name ) )
  | FArrow {polymorphic= Some ty'; _}, Id i
  | FConstructor {polymorphic= Some ty'; _}, Id i ->
      bind_type_id i ty' cxt
  | FConstructor {parameters= []; polymorphic= None; _}, _ ->
      failwith "fast_unify: parameterless constructor is not monomorphic"
  | FArrow {left= f_l; right= f_r; polymorphic= None}, Id i ->
      let l, cxt = make_type_id cxt in
      let r, cxt = make_type_id cxt in
      let a : arrow_signature = {left= l; right= r; polymorphic= true} in
      let cxt = bind_type_id i (Arrow a) cxt in
      let cxt = fast_unify cxt f_l l in
      fast_unify cxt f_r l
  | FConstructor {name; parameters= fast_parameters; polymorphic= None}, Id i ->
      let parameters, cxt = make_type_ids (List.length fast_parameters) cxt in
      let c : cons_signature = {name; parameters; polymorphic= true} in
      let cxt = bind_type_id i (Constructor c) cxt in
      List.fold2_exn fast_parameters parameters ~init:cxt ~f:fast_unify
  | FArrow _, Constructor _ | FConstructor _, Arrow _ ->
      raise (UnificationFailure "constructor does not unify with arrow")

let make_fast_unifier ty =
  let fast_ty, types = fast_of_slow ty in
  fun cxt req ->
    let decomposition = align fast_ty req in
    if Option.is_none decomposition then
      raise
        (UnificationFailure
           (Format.sprintf "%s does not unify with %s" (string_of_dc_type req)
              (string_of_dc_type ty) ) ) ;
    let parameters_fast_ty, terminal_fast_ty = Util.value_exn decomposition in
    let cxt = fast_unify cxt terminal_fast_ty req in
    let next_id = cxt.next_id in
    let next_id_ref = ref next_id in
    let parameters =
      List.map parameters_fast_ty ~f:(slow_of_fast next_id_ref)
    in
    let cxt = snd @@ make_type_ids (!next_id_ref - next_id) cxt in
    Array.iter types ~f:(fun ty_opt -> ty_opt := None) ;
    (cxt, parameters)