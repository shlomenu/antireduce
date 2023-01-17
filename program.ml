open Core
open Type

type primitive = {name: string; ty: dc_type}
[@@deriving yojson, equal, compare, sexp_of, hash]

type invention =
  { name: string [@equal.ignore] [@compare.ignore]
  ; ty: dc_type [@equal.ignore] [@compare.ignore]
  ; body: program }
[@@deriving yojson, equal, compare, sexp_of, hash]

and program =
  | Index of int
  | Abstraction of program
  | Apply of program * program
  | Primitive of primitive
  | Invented of invention
[@@deriving yojson, equal, compare, sexp_of, hash]

module Program = struct
  type t = program [@@deriving equal, compare, sexp_of, hash]

  include Comparator.Make (struct
    type t = program [@@deriving equal, compare, sexp_of, hash]
  end)
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

let rec mass_of_program = function
  | Apply (f, x) ->
      mass_of_program f + mass_of_program x
  | Abstraction b ->
      mass_of_program b
  | Index _ | Primitive _ ->
      1
  | Invented {body; _} ->
      mass_of_program body

let rec subexpressions p =
  let subexprs = List.map (child_programs p) ~f:subexpressions |> List.concat in
  p :: subexprs

let string_of_program
    ?(format : [`Stitch | `Dreamcoder | `Combined] = `Combined) :
    program -> string =
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

let primitive_name = function
  | Primitive {name; _} ->
      name
  | _ ->
      failwith "primitive_name: not base primitive"

exception UnboundVariable

let rec infer_type cxt env = function
  | Index i ->
      apply_context cxt @@ List.nth_exn env i
  | Primitive {ty; _} | Invented {ty; _} ->
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

let invention name body =
  let ty = canonical_type @@ closed_inference body in
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

type annotated_expr =
  | AIndex of dc_type * int
  | APrimitive of dc_type * string
  | AApply of dc_type * dc_type * dc_type * annotated_expr * annotated_expr
  | AAbstraction of dc_type * annotated_expr

let string_of_annotated_expr =
  let rec go parenthesized cxt = function
    | AIndex (ty, j) ->
        let _, ty = apply_context cxt ty in
        "($" ^ string_of_int j ^ " : " ^ string_of_dc_type ty ^ ")"
    | AAbstraction (ty, b) ->
        let cxt, ty = apply_context cxt ty in
        "((lambda " ^ go true cxt b ^ ") : " ^ string_of_dc_type ty ^ ")"
    | AApply (_, _, _, f, x) ->
        let body = go false cxt f ^ " " ^ go true cxt x in
        if parenthesized then "(" ^ body ^ ")" else body
    | APrimitive (ty, name) ->
        let _, ty = apply_context cxt ty in
        "(" ^ name ^ " : " ^ string_of_dc_type ty ^ ")"
  in
  go true

let rec instantiate_all cxt env = function
  | Index i ->
      let ty = List.nth_exn env i in
      (cxt, ty, AIndex (ty, i))
  | Primitive {name; ty} ->
      let cxt, ty = instantiate_type cxt ty in
      (cxt, ty, APrimitive (ty, name))
  | Invented {body; _} ->
      instantiate_all cxt [] body
  | Abstraction b ->
      let parameter_type, cxt = make_type_id cxt in
      let cxt, terminal_type, b' =
        instantiate_all cxt (parameter_type :: env) b
      in
      let function_type = parameter_type @> terminal_type in
      (cxt, function_type, AAbstraction (function_type, b'))
  | Apply (f, x) ->
      let cxt, function_type, f' = instantiate_all cxt env f in
      let cxt, parameter_type, x' = instantiate_all cxt env x in
      let cxt, terminal_type =
        match function_type with
        | Id _ ->
            let terminal_type, cxt = make_type_id cxt in
            (cxt, terminal_type)
        | Arrow {right; _} ->
            (cxt, right)
        | Constructor _ ->
            failwith
            @@ Format.sprintf "function_type is not an arrow: %s"
            @@ string_of_annotated_expr cxt f'
      in
      let cxt = unify cxt function_type (parameter_type @> terminal_type) in
      ( cxt
      , terminal_type
      , AApply (terminal_type, function_type, parameter_type, f', x') )

let rec unify_all cxt req = function
  | AIndex (ty, _) | APrimitive (ty, _) ->
      unify cxt req ty
  | AAbstraction (function_type, b) ->
      let cxt = unify cxt req function_type in
      unify_all cxt (right_of_arrow req) b
  | AApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt = unify cxt req terminal_type in
      let cxt = unify_all cxt function_type f in
      unify_all cxt parameter_type x

let rec apply_context_all cxt = function
  | AIndex (ty, i) ->
      let _, ty' = apply_context cxt ty in
      AIndex (ty', i)
  | APrimitive (ty, name) ->
      let _, ty' = apply_context cxt ty in
      APrimitive (ty', name)
  | AAbstraction (function_type, b) ->
      let cxt, function_type' = apply_context cxt function_type in
      AAbstraction (function_type', apply_context_all cxt b)
  | AApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt, terminal_type' = apply_context cxt terminal_type in
      let cxt, function_type' = apply_context cxt function_type in
      let cxt, parameter_type' = apply_context cxt parameter_type in
      let f' = apply_context_all cxt f in
      let x' = apply_context_all cxt x in
      AApply (terminal_type', function_type', parameter_type', f', x')

type generic_expr =
  | GIndex of int
  | GPrimitive of string
  | GApply of generic_expr * generic_expr
  | GAbstraction of dc_type * generic_expr

let string_of_generic_expr =
  let rec go parenthesized cxt = function
    | GIndex j ->
        "$" ^ string_of_int j
    | GAbstraction (ty, b) ->
        let cxt, ty = apply_context cxt ty in
        "(lambda (" ^ string_of_dc_type ty ^ ") " ^ go true cxt b ^ ")"
    | GApply (f, x) ->
        let body = go false cxt f ^ " " ^ go true cxt x in
        if parenthesized then "(" ^ body ^ ")" else body
    | GPrimitive name ->
        name
  in
  go true

let rec generic_of_annotated = function
  | AIndex (_, i) ->
      GIndex i
  | APrimitive (_, name) ->
      GPrimitive name
  | AApply (_, _, _, f, x) ->
      GApply (generic_of_annotated f, generic_of_annotated x)
  | AAbstraction (function_type, b) ->
      GAbstraction (left_of_arrow function_type, generic_of_annotated b)

let generic_expr_of_program req p =
  let cxt, _, ap =
    instantiate_all empty_type_context []
    @@ beta_normal_form ~reduce_invented:true p
  in
  let cxt = unify_all cxt req ap in
  generic_of_annotated @@ apply_context_all cxt ap
