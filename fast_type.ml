open Core

type cons = {name: string; parameters: t list; polymorphic: Type.t option}

and arr = {left: t; right: t; polymorphic: Type.t option}

and t = FId of Type.t option ref | FArrow of arr | FConstructor of cons

let to_string : t -> string =
  let rec go parenthesized = function
    | FId i ->
        Option.value_map !i ~default:"t?" ~f:Type.to_string
    | FArrow {left; right; _} ->
        let body = go true left ^ " -> " ^ go false right in
        if parenthesized then "(" ^ body ^ ")" else body
    | FConstructor {name; parameters; _} ->
        if List.is_empty parameters then name
        else
          let params =
            List.map parameters ~f:(go false) |> String.concat ~sep:", "
          in
          name ^ "(" ^ params ^ ")"
  in
  go false

let of_type ty =
  let ty = Type.to_canonical ty in
  let next_id = Type.next_type_var ty in
  let types = Array.init next_id ~f:(fun _ -> ref None) in
  let rec go : Type.t -> t = function
    | Id i ->
        FId (Array.get types i)
    | Arrow a as ty ->
        FArrow
          { left= go a.left
          ; right= go a.right
          ; polymorphic= (if a.polymorphic then None else Some ty) }
    | Constructor c as ty ->
        FConstructor
          { name= c.name
          ; parameters= List.map c.parameters ~f:go
          ; polymorphic= (if c.polymorphic then None else Some ty) }
  in
  (go ty, types)

let rec to_type next_id_ref = function
  | FArrow a ->
      Type.arrow (to_type next_id_ref a.left) (to_type next_id_ref a.right)
  | FConstructor con ->
      Type.kind con.name @@ List.map con.parameters ~f:(to_type next_id_ref)
  | FId ({contents= ty_opt} as ty_opt_ref) -> (
    match ty_opt with
    | Some ty ->
        ty
    | None ->
        let ty : Type.t = Id !next_id_ref in
        incr next_id_ref ;
        ty_opt_ref := Some ty ;
        ty )
