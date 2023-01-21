open Core

type t =
  { dc_name: string
  ; stitch_name: string
  ; ty: Type.t
  ; impl: Program.t option
  ; log_likelihood: float
  ; unifier: Type_context.t -> Type.t -> (Type_context.t * Type.t list) list }
[@@deriving fields]

let yojson_of_t ent =
  `Assoc
    [ ("dc_name", yojson_of_string ent.dc_name)
    ; ("stitch_name", yojson_of_string ent.stitch_name)
    ; ("ty", Type.yojson_of_t ent.ty)
    ; ("impl", yojson_of_option Program.yojson_of_t ent.impl)
    ; ("log_likelihood", yojson_of_float ent.log_likelihood) ]

let t_of_yojson = function
  | `Assoc
      [ ("dc_name", j_dc_name)
      ; ("stitch_name", j_stitch_name)
      ; ("ty", j_ty)
      ; ("impl", j_impl)
      ; ("log_likelihood", j_ll) ] ->
      let ty = Type.t_of_yojson j_ty in
      { dc_name= string_of_yojson j_dc_name
      ; stitch_name= string_of_yojson j_stitch_name
      ; ty
      ; impl= option_of_yojson Program.t_of_yojson j_impl
      ; unifier= Fast_type.unifier ty
      ; log_likelihood= float_of_yojson j_ll }
  | _ ->
      failwith "primitive_entry_of_yojson: invalid json"

let to_primitive ent : Program.t =
  match ent.impl with
  | None ->
      Primitive {name= ent.dc_name; ty= ent.ty}
  | Some body ->
      Invented {name= ent.stitch_name; ty= ent.ty; body}

let of_primitive log_likelihood : Program.t -> t = function
  | Primitive {name; ty} ->
      { dc_name= name
      ; stitch_name= name
      ; ty
      ; impl= None
      ; unifier= Fast_type.unifier ty
      ; log_likelihood }
  | Invented {name; ty; body} ->
      { dc_name= Program.to_string body
      ; stitch_name= name
      ; ty
      ; impl= Some body
      ; unifier= Fast_type.unifier ty
      ; log_likelihood }
  | _ ->
      failwith "dsl_of_primitives: not a base primitive"
