open Core
open Type

type primitive = {name: string; ty: dc_type}
[@@deriving yojson, equal, compare, sexp_of, hash]

type program =
  | Index of int
  | Abstraction of program
  | Apply of program * program
  | Primitive of primitive
  | Invented of (dc_type[@equal.ignore] [@compare.ignore]) * program
[@@deriving yojson, equal, compare, sexp_of, hash]

module Program = struct
  type t = program [@@deriving compare, sexp_of, hash]
end

let is_index = function Index _ -> true | _ -> false

let int_of_index = function
  | Index n ->
      n
  | _ ->
      failwith "int_of_index: not an index"

let is_primitive = function Primitive _ | Invented _ -> true | _ -> false

let is_base_primitive = function Primitive _ -> true | _ -> false

let is_abstraction = function Abstraction _ -> true | _ -> false

let rec strip_abstractions = function
  | Abstraction b ->
      strip_abstractions b
  | e ->
      e

let rec wrap_abstractions n e =
  if n > 0 then wrap_abstractions (n - 1) (Abstraction e) else e

let child_programs = function
  | Abstraction b ->
      [b]
  | Apply (f, x) ->
      [f; x]
  | _ ->
      []

let rec function_of_application = function
  | Apply (f, _) ->
      function_of_application f
  | e ->
      e

let rec unpack_application = function
  | Apply (f, x) ->
      let f, arguments = unpack_application f in
      (f, arguments @ [x])
  | e ->
      (e, [])

let rec size_of_program = function
  | Apply (f, x) ->
      size_of_program f + size_of_program x
  | Abstraction b ->
      size_of_program b
  | Index _ | Invented _ | Primitive _ ->
      1

let rec subexpressions p =
  let subexprs = List.map (child_programs p) ~f:subexpressions |> List.concat in
  p :: subexprs

let string_of_program : program -> string =
  let rec go parenthesized = function
    | Index j ->
        "$" ^ string_of_int j
    | Abstraction b ->
        "(lambda " ^ go true b ^ ")"
    | Apply (f, x) ->
        let body = go false f ^ " " ^ go true x in
        if parenthesized then "(" ^ body ^ ")" else body
    | Primitive {name; _} ->
        name
    | Invented (_, b) ->
        "#" ^ go true b
  in
  go true

let primitive_name = function
  | Primitive {name; _} ->
      name
  | _ ->
      failwith "primitive_name: not base primitive"

exception UnboundVariable

let rec infer_type cxt env = function
  | Index i ->
      apply_context cxt @@ List.nth_exn env i
  | Primitive {ty; _} | Invented (ty, _) ->
      instantiate_type cxt ty
  | Abstraction b ->
      let parameter_ty, cxt = make_type_id cxt in
      let cxt, terminal_ty = infer_type cxt (parameter_ty :: env) b in
      apply_context cxt (parameter_ty @> terminal_ty)
  | Apply (f, x) ->
      let terminal_ty, cxt = make_type_id cxt in
      let cxt, parameter_ty = infer_type cxt env x in
      let cxt, application_ty = infer_type cxt env f in
      let cxt = unify cxt application_ty (parameter_ty @> terminal_ty) in
      apply_context cxt terminal_ty

let closed_inference p : dc_type = snd @@ infer_type empty_type_context [] p

let invention b =
  let ty = canonical_type @@ closed_inference b in
  Invented (ty, b)

let rec make_app_n ?(c = 0) p n =
  if c = n then
    match List.range ~stride:(-1) ~start:`exclusive ~stop:`inclusive n 0 with
    | i :: is ->
        let init = Apply (p, Index i) in
        List.fold is ~init ~f:(fun app i -> Apply (app, Index i))
    | [] ->
        failwith "make_app_n: n must be greater than zero"
  else Abstraction (make_app_n ~c:(c + 1) p n)

let rec strip_n_abstractions (n : int) (p : program) : program =
  match (n, p) with
  | 0, p ->
      p
  | n, Abstraction b ->
      strip_n_abstractions (n - 1) b
  | _ ->
      failwith "strip_n_abstractions: fewer than n abstractions"

let rec index_is_bound ?(i = 0) = function
  | Index j ->
      j = i
  | Apply (f, x) ->
      index_is_bound ~i f || index_is_bound ~i x
  | Invented (_, b) ->
      index_is_bound ~i b
  | Primitive _ ->
      false
  | Abstraction b ->
      index_is_bound ~i:(i + 1) b

exception ShiftFailure

let rec shift_free_variables ?(height = 0) shift = function
  | Index j as p ->
      if j < height then p
      else if j + shift < 0 then raise ShiftFailure
      else Index (j + shift)
  | Apply (f, x) ->
      let f = shift_free_variables ~height shift f in
      let x = shift_free_variables ~height shift x in
      Apply (f, x)
  | (Invented _ | Primitive _) as p ->
      p
  | Abstraction b ->
      let b = shift_free_variables ~height:(height + 1) shift b in
      Abstraction b

let rec free_variables ?(d = 0) = function
  | Index j ->
      if j >= d then [j - d] else []
  | Apply (f, x) ->
      free_variables ~d f @ free_variables ~d x
  | Abstraction b ->
      free_variables ~d:(d + 1) b
  | _ ->
      []

let rec substitute i v = function
  | Index j as p ->
      if i = j then v else p
  | Abstraction b ->
      let b = substitute (i + 1) (shift_free_variables 1 v) b in
      Abstraction b
  | Apply (f, x) ->
      let f = substitute i v f in
      let x = substitute i v x in
      Apply (f, x)
  | p ->
      p

let rec beta_normal_form ?(reduce_invented = false) p =
  let rec step = function
    | Abstraction b -> (
      match step b with Some b' -> Some (Abstraction b') | None -> None )
    | Invented (_, b) when reduce_invented ->
        Some b
    | Apply (f, x) -> (
      match step f with
      | Some f' ->
          Some (Apply (f', x))
      | None -> (
        match step x with
        | Some x' ->
            Some (Apply (f, x'))
        | None -> (
          match f with
          | Abstraction b ->
              Some
                (shift_free_variables (-1)
                   (substitute 0 (shift_free_variables 1 x) b) )
          | _ ->
              None ) ) )
    | _ ->
        None
  in
  let f = beta_normal_form ~reduce_invented in
  Option.value_map (step p) ~f ~default:p

let rec remove_decorative_abstractions ?(n = -1) ?(k = 0) = function
  | Abstraction b ->
      remove_decorative_abstractions ~n:(n + 1) b
  | Apply (f, Index i) when i = k && k <> n ->
      remove_decorative_abstractions ~n ~k:(k + 1) f
  | Apply (f, Index i) when i = k && k = n ->
      Some f
  | _ ->
      None