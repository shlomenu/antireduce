open Core

type t =
  | ATIndex of int
  | ATPrimitive of string
  | ATApply of t * t
  | ATAbstraction of Type.t * t

let to_string =
  let rec go parenthesized cxt = function
    | ATIndex j ->
        "$" ^ string_of_int j
    | ATAbstraction (ty, b) ->
        let cxt, ty = Type_context.apply cxt ty in
        "(lambda (" ^ Type.to_string ty ^ ") " ^ go true cxt b ^ ")"
    | ATApply (f, x) ->
        let body = go false cxt f ^ " " ^ go true cxt x in
        if parenthesized then "(" ^ body ^ ")" else body
    | ATPrimitive name ->
        name
  in
  go true

let rec of_typed_program : Typed_program.t -> t = function
  | TIndex (_, i) ->
      ATIndex i
  | TPrimitive (_, name) ->
      ATPrimitive name
  | TApply (_, _, _, f, x) ->
      ATApply (of_typed_program f, of_typed_program x)
  | TAbstraction (function_type, b) ->
      ATAbstraction (Type.left_of_arrow function_type, of_typed_program b)

let of_program req p =
  let cxt, _, ap =
    Typed_program.instantiate ~reduce_invented:true Type_context.empty []
    @@ Program.beta_normal_form ~reduce_invented:true p
  in
  let cxt = Typed_program.unify cxt req ap in
  of_typed_program @@ Typed_program.apply_context cxt ap
