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

let rec enumerate_terminal dsl cxt req search_points =
  match req with
  | Arrow {right; _} ->
      enumerate_terminal dsl cxt right search_points
      |> Option.value_map ~default:None ~f:(fun (b, cxt', prims') ->
             Some (PAbstraction b, cxt', prims') )
  | _ -> (
    match search_points with
    | point :: rest ->
        let rec go remaining_unified =
          let location = min (List.length remaining_unified - 1) point in
          let selected = List.nth_exn remaining_unified location in
          let unselected =
            List.filteri remaining_unified ~f:(fun i _ -> i <> location)
          in
          match
            enumerate_parameters dsl cxt selected.parameters
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

and enumerate_parameters dsl cxt parameters f search_points =
  match parameters with
  | [] ->
      Some (f, cxt, search_points)
  | last :: [] when equal_dc_type last dsl.state_type ->
      Some (PApply (f, PIndex 0), cxt, search_points)
  | x_1_ty :: rest ->
      if List.length parameters > List.length search_points then None
      else
        let cxt, x_1_ty = apply_context cxt x_1_ty in
        enumerate_terminal dsl cxt x_1_ty search_points
        |> Option.value_map ~default:None ~f:(fun (x_1, cxt', search_points') ->
               enumerate_parameters dsl cxt' rest
                 (PApply (f, x_1))
                 search_points' )

let commands_to_program req dsl search_points =
  if not (equal_dc_type req @@ arrow dsl.state_type dsl.state_type) then
    failwith
      "commands_to_program: requested type must be of the form: dsl.state_type \
       -> dsl.state_type" ;
  enumerate_terminal dsl empty_type_context req search_points
  |> Option.value_map ~default:None ~f:(fun (p, _, prim_indices') ->
         Some (program_of_partial p, List.length prim_indices') )
