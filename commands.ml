open Core
open Type
open Program
open Grammar

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

let rec enumerate_argument gmr cxt req env prims =
  match req with
  | Arrow {left; right; _} ->
      Option.value_map ~default:None ~f:(fun (b, cxt', log_prob, prims') ->
          Some (PAbstraction b, cxt', log_prob, prims') )
      @@ enumerate_argument gmr cxt right (left :: env) prims
  | _ -> (
    match prims with
    | prim :: rest -> (
      match
        unifying_expressions gmr env req cxt
        |> List.filter_map ~f:(fun ue ->
               if equal_program prim ue.expr then Some ue else None )
      with
      | e_f :: _ ->
          Option.value_map ~default:None
            ~f:(fun (f_applied, cxt', log_prob_args, prims') ->
              Some (f_applied, cxt', log_prob_args +. e_f.log_prob, prims') )
          @@ enumerate_application gmr cxt env e_f.parameters
               (partial_of_program e_f.expr)
               rest
      | _ ->
          None )
    | _ ->
        None )

and enumerate_application gmr cxt env parameters f prims =
  match parameters with
  | [] ->
      Some (f, cxt, 0.0, prims)
  | x_1 :: rest ->
      let cxt, x_1 = apply_context cxt x_1 in
      Option.value_map ~default:None
        ~f:(fun (x_1, cxt', log_prob_x_1, prims') ->
          Option.value_map ~default:None
            ~f:(fun (xs, cxt'', log_prob_rest, prims'') ->
              Some (xs, cxt'', log_prob_x_1 +. log_prob_rest, prims'') )
          @@ enumerate_application gmr cxt' env rest (PApply (f, x_1)) prims' )
      @@ enumerate_argument gmr cxt x_1 env prims

let commands_to_program req gmr prim_indices =
  enumerate_argument gmr empty_type_context req [] prim_indices
  |> Option.value_map ~default:None ~f:(fun (p, _, _, prim_indices') ->
         Some (program_of_partial p, List.length prim_indices') )
