open Core
open Type
open Program
open Dsl

type partial_program =
  | PIndex of int
  | PAbstraction of partial_program
  | PApply of partial_program * partial_program
  | PPrimitive of primitive
  | PInvented of dc_type * program
  | Hole of dc_type

let rec partial_of_program = function
  | Index i ->
      PIndex i
  | Abstraction b ->
      PAbstraction (partial_of_program b)
  | Apply (f, x) ->
      PApply (partial_of_program f, partial_of_program x)
  | Primitive prim ->
      PPrimitive prim
  | Invented (ty, b) ->
      PInvented (ty, b)

let rec program_of_partial = function
  | PIndex i ->
      Index i
  | PAbstraction b ->
      Abstraction (program_of_partial b)
  | PApply (f, x) ->
      Apply (program_of_partial f, program_of_partial x)
  | PPrimitive prim ->
      Primitive prim
  | PInvented (ty, b) ->
      Invented (ty, b)
  | Hole _ ->
      failwith "cannot convert partial program with holes to program"

let string_of_partial_program (p : partial_program) : string =
  let rec go parenthesized : partial_program -> string = function
    | PIndex j ->
        "$" ^ string_of_int j
    | PAbstraction b ->
        "(lambda " ^ go true b ^ ")"
    | PApply (f, x) ->
        let body = go false f ^ " " ^ go true x in
        if parenthesized then "(" ^ body ^ ")" else body
    | PPrimitive {name; _} ->
        name
    | PInvented (_, b) ->
        "#" ^ string_of_program b
    | Hole ty ->
        Printf.sprintf "<%s>" (string_of_dc_type ty)
  in
  go true p

let select_at_point (ues : unifying_expression list) (point : float) :
    unifying_expression list * unifying_expression =
  let n_exprs = List.length ues in
  let location =
    min (n_exprs - 1)
    @@ int_of_float
    @@ Float.round_nearest (point *. (float_of_int @@ n_exprs))
  in
  (List.filteri ues ~f:(fun i _ -> i <> location), List.nth_exn ues location)

let rec enumerate_argument dsl cxt req env search_points =
  match req with
  | Arrow {left; right; _} ->
      Option.value_map ~default:None ~f:(fun (b, cxt', prims') ->
          Some (PAbstraction b, cxt', prims') )
      @@ enumerate_argument dsl cxt right (left :: env) search_points
  | _ -> (
    match search_points with
    | point :: rest ->
        let rec go remaining_unified =
          let unselected, selected = select_at_point remaining_unified point in
          match
            enumerate_application dsl cxt env selected.parameters
              (partial_of_program selected.expr)
              rest
          with
          | Some _ as r ->
              r
          | None ->
              if List.is_empty unselected then None else go unselected
        in
        go @@ unifying_primitives dsl req cxt
    | _ ->
        None )

and enumerate_application dsl cxt env parameters f search_points =
  match parameters with
  | [] ->
      Some (f, cxt, search_points)
  | x_1_ty :: rest ->
      if List.length parameters > List.length search_points then None
      else
        let cxt, x_1_ty = apply_context cxt x_1_ty in
        enumerate_argument dsl cxt x_1_ty env search_points
        |> Option.value_map ~default:None ~f:(fun (x_1, cxt', search_points') ->
               enumerate_application dsl cxt' env rest
                 (PApply (f, x_1))
                 search_points' )

let commands_to_program req gmr search_points =
  enumerate_argument gmr empty_type_context req [] search_points
  |> Option.value_map ~default:None ~f:(fun (p, _, prim_indices') ->
         Some (program_of_partial p, List.length prim_indices') )
