open Core

type t =
  | TIndex of Type.t * int
  | TPrimitive of Type.t * string
  | TApply of Type.t * Type.t * Type.t * t * t
  | TAbstraction of Type.t * t

let to_string =
  let rec go parenthesized cxt = function
    | TIndex (ty, j) ->
        let _, ty = Type_context.apply cxt ty in
        "($" ^ string_of_int j ^ " : " ^ Type.to_string ty ^ ")"
    | TAbstraction (ty, b) ->
        let cxt, ty = Type_context.apply cxt ty in
        "((lambda " ^ go true cxt b ^ ") : " ^ Type.to_string ty ^ ")"
    | TApply (_, _, _, f, x) ->
        let body = go false cxt f ^ " " ^ go true cxt x in
        if parenthesized then "(" ^ body ^ ")" else body
    | TPrimitive (ty, name) ->
        let _, ty = Type_context.apply cxt ty in
        "(" ^ name ^ " : " ^ Type.to_string ty ^ ")"
  in
  go true

let rec instantiate ~reduce_invented cxt env :
    Program.t -> Type_context.t * Type.t * t = function
  | Index i ->
      let ty = List.nth_exn env i in
      (cxt, ty, TIndex (ty, i))
  | Primitive {name; ty} ->
      let cxt, ty = Type_context.instantiate cxt ty in
      (cxt, ty, TPrimitive (ty, name))
  | Invented {name; ty; body} ->
      if reduce_invented then instantiate ~reduce_invented cxt [] body
      else
        let cxt, ty = Type_context.instantiate cxt ty in
        (cxt, ty, TPrimitive (ty, name))
  | Abstraction b ->
      let parameter_type, cxt = Type_context.make_id cxt in
      let cxt, terminal_type, b' =
        instantiate ~reduce_invented cxt (parameter_type :: env) b
      in
      let function_type = Type.(parameter_type @> terminal_type) in
      (cxt, function_type, TAbstraction (function_type, b'))
  | Apply (f, x) ->
      let cxt, function_type, f' = instantiate ~reduce_invented cxt env f in
      let cxt, parameter_type, x' = instantiate ~reduce_invented cxt env x in
      let cxt, terminal_type =
        match function_type with
        | Id _ ->
            let terminal_type, cxt = Type_context.make_id cxt in
            (cxt, terminal_type)
        | Arrow {right; _} ->
            (cxt, right)
        | Constructor _ ->
            failwith
            @@ Format.sprintf "function_type is not an arrow: %s"
            @@ to_string cxt f'
      in
      let cxt =
        Type_unification.unify cxt function_type
          Type.(parameter_type @> terminal_type)
      in
      ( cxt
      , terminal_type
      , TApply (terminal_type, function_type, parameter_type, f', x') )

let rec unify cxt req = function
  | TIndex (ty, _) | TPrimitive (ty, _) ->
      Type_unification.unify cxt req ty
  | TAbstraction (function_type, b) ->
      let cxt = Type_unification.unify cxt req function_type in
      unify cxt (Type.right_of_arrow req) b
  | TApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt = Type_unification.unify cxt req terminal_type in
      let cxt = unify cxt function_type f in
      unify cxt parameter_type x

let rec apply_context cxt = function
  | TIndex (ty, i) ->
      let _, ty' = Type_context.apply cxt ty in
      TIndex (ty', i)
  | TPrimitive (ty, name) ->
      let _, ty' = Type_context.apply cxt ty in
      TPrimitive (ty', name)
  | TAbstraction (function_type, b) ->
      let cxt, function_type' = Type_context.apply cxt function_type in
      TAbstraction (function_type', apply_context cxt b)
  | TApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt, terminal_type' = Type_context.apply cxt terminal_type in
      let cxt, function_type' = Type_context.apply cxt function_type in
      let cxt, parameter_type' = Type_context.apply cxt parameter_type in
      TApply
        ( terminal_type'
        , function_type'
        , parameter_type'
        , apply_context cxt f
        , apply_context cxt x )

let rec list_of_applications terminal_type = function
  | TApply (_, _, parameter_type, f, x) ->
      list_of_applications terminal_type f @ [(parameter_type, x)]
  | f ->
      [(terminal_type, f)]
