open Core

module T = struct
  type primitive = {name: string; ty: Type.t}
  [@@deriving yojson, equal, compare, sexp_of, hash]

  type invention =
    { name: string [@equal.ignore] [@compare.ignore]
    ; ty: Type.t [@equal.ignore] [@compare.ignore]
    ; body: t }
  [@@deriving yojson, equal, compare, sexp_of, hash]

  and t =
    | Index of int
    | Abstraction of t
    | Apply of t * t
    | Primitive of primitive
    | Invented of invention
  [@@deriving yojson, equal, compare, sexp_of, hash]
end

include T
include Comparator.Make (T)

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

let children = function
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

let rec size = function
  | Apply (f, x) ->
      size f + size x
  | Abstraction b ->
      size b
  | Index _ | Invented _ | Primitive _ ->
      1

let rec mass = function
  | Apply (f, x) ->
      mass f + mass x
  | Abstraction b ->
      mass b
  | Index _ | Primitive _ ->
      1
  | Invented {body; _} ->
      mass body

let rec subexpressions p =
  let subexprs = List.map (children p) ~f:subexpressions |> List.concat in
  p :: subexprs

let to_string ?(format : [`Stitch | `Dreamcoder | `Combined] = `Combined) :
    t -> string =
  let rec go parenthesized = function
    | Index j ->
        "$" ^ string_of_int j
    | Abstraction b -> (
        let body = go true b in
        match format with
        | `Stitch | `Combined ->
            "(lam " ^ body ^ ")"
        | `Dreamcoder ->
            "(lambda " ^ body ^ ")" )
    | Apply (f, x) ->
        let body = go false f ^ " " ^ go true x in
        if parenthesized then "(" ^ body ^ ")" else body
    | Primitive {name; _} ->
        name
    | Invented {name; body; _} -> (
      match format with
      | `Stitch ->
          name
      | `Dreamcoder ->
          "#" ^ go true body
      | `Combined ->
          "{" ^ name ^ "}" ^ go true body )
  in
  go true

let name_of_primitive = function
  | Primitive {name; _} ->
      name
  | Invented {name; _} ->
      name
  | _ ->
      failwith "primitive_name: not a primitive"

let rec infer_type cxt env = function
  | Index i ->
      Type_context.apply cxt @@ List.nth_exn env i
  | Primitive {ty; _} | Invented {ty; _} ->
      Type_context.instantiate cxt ty
  | Abstraction b ->
      let parameter_ty, cxt = Type_context.make_id cxt in
      let cxt, terminal_ty = infer_type cxt (parameter_ty :: env) b in
      Type_context.apply cxt Type.(parameter_ty @> terminal_ty)
  | Apply (f, x) ->
      let terminal_ty, cxt = Type_context.make_id cxt in
      let cxt, parameter_ty = infer_type cxt env x in
      let cxt, application_ty = infer_type cxt env f in
      let cxt =
        Type_unification.unify cxt application_ty
          Type.(parameter_ty @> terminal_ty)
      in
      Type_context.apply cxt terminal_ty

let closed_inference p : Type.t = snd @@ infer_type Type_context.empty [] p

let invention name body =
  let ty = Type.to_canonical @@ closed_inference body in
  Invented {name; ty; body}

let rec make_app_n ?(c = 0) p n =
  if c = n then
    match List.range ~stride:(-1) ~start:`exclusive ~stop:`inclusive n 0 with
    | i :: is ->
        let init = Apply (p, Index i) in
        List.fold is ~init ~f:(fun app i -> Apply (app, Index i))
    | [] ->
        failwith "make_app_n: n must be greater than zero"
  else Abstraction (make_app_n ~c:(c + 1) p n)

let rec index_is_bound ?(i = 0) = function
  | Index j ->
      j = i
  | Apply (f, x) ->
      index_is_bound ~i f || index_is_bound ~i x
  | Invented {body; _} ->
      index_is_bound ~i body
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

exception UnboundVariable

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
    | Invented {body; _} when reduce_invented ->
        Some body
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
