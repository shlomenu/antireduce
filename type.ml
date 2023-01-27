open Core

module T = struct
  type cons = {name: string; parameters: t list; polymorphic: bool}
  [@@deriving compare, hash, sexp_of, yojson]

  and arr = {left: t; right: t; polymorphic: bool}
  [@@deriving compare, hash, sexp_of, yojson]

  and t = Id of int | Constructor of cons | Arrow of arr
  [@@deriving compare, hash, sexp_of, yojson]

  let rec equal ty_a ty_b =
    match (ty_a, ty_b) with
    | Id id_a, Id id_b ->
        id_a = id_b
    | Constructor con_a, Constructor con_b ->
        String.(con_a.name = con_b.name)
        && List.equal equal con_a.parameters con_b.parameters
    | Arrow arw_a, Arrow arw_b ->
        equal arw_a.left arw_b.left && equal arw_a.right arw_b.right
    | _ ->
        false
end

include T
include Comparator.Make (T)

let rec size = function
  | Id _ ->
      1
  | Constructor {parameters; _} ->
      1
      + List.fold parameters ~init:0 ~f:(fun size' param -> size' + size param)
  | Arrow {left; right; _} ->
      size left + size right

let is_polymorphic = function
  | Id _ ->
      true
  | Constructor {polymorphic; _} | Arrow {polymorphic; _} ->
      polymorphic

let kind name parameters =
  let polymorphic = List.exists parameters ~f:is_polymorphic in
  Constructor {name; parameters; polymorphic}

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

let rec parameters_and_terminal = function
  | Arrow {left; right; _} ->
      let parameters, terminal = parameters_and_terminal right in
      (left :: parameters, terminal)
  | ty ->
      ([], ty)

let rec terminal = function Arrow {right; _} -> terminal right | ty -> ty

let rec parameters = function
  | Arrow {left; right; _} ->
      left :: parameters right
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

let to_string : t -> string =
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

let rec occurs i = function
  | ty when not (is_polymorphic ty) ->
      false
  | Arrow {left; right; _} ->
      occurs i left || occurs i right
  | Constructor {parameters; _} ->
      List.exists parameters ~f:(occurs i)
  | Id j ->
      j = i

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

let rec arity = function Arrow {right; _} -> 1 + arity right | _ -> 0

let ground name = Constructor {name; parameters= []; polymorphic= false}

let to_canonical ?next_id_ref ?types ty =
  let next_id_ref = match next_id_ref with Some r -> r | None -> ref 0 in
  let types = match types with Some types -> types | None -> ref [] in
  let rec go = function
    | Id i -> (
      try Id (List.Assoc.find_exn ~equal:Int.equal !types i)
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
