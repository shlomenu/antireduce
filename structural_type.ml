open Core

module T = struct
  type t = (Type_context.t option[@sexp.opaque]) * Type.t [@@deriving sexp_of]

  let equal (cxt_1_opt, ty_1) (_, ty_2) =
    match cxt_1_opt with
    | Some cxt_1 -> (
      try
        ignore (Type_unification.unify cxt_1 ty_1 ty_2 : Type_context.t) ;
        true
      with Type_unification.UnificationFailure _ -> false )
    | None ->
        failwith "Structural_type.equal: missing reference context"

  let compare ((cxt_1_opt, ty_1) as st_1) ((_, ty_2) as st_2) =
    match cxt_1_opt with
    | Some cxt_1 ->
        if equal st_1 st_2 then 0
        else
          let _, ty_1' = Type_context.apply cxt_1 ty_1 in
          Type.compare ty_1' ty_2
    | None ->
        Type.compare ty_1 ty_2
end

include T
include Comparator.Make (T)

let of_contextual_type cxt ty : t = (None, snd @@ Type_context.apply cxt ty)

let of_type (ty : Type.t) : t = (None, ty)
