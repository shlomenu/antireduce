open Core

type cons = {name: string; parameters: t list; polymorphic: Type.t option}

and arr = {left: t; right: t; polymorphic: Type.t option}

and t = FId of Type.t option ref | FArrow of arr | FConstructor of cons

let rec aligned fast_ty (ty : Type.t) =
  match (fast_ty, ty) with
  | FArrow {right= fast_right; _}, Arrow {right; _} ->
      aligned fast_right right
  | _, Id _ | FId _, _ | FConstructor _, Constructor _ ->
      true
  | FArrow _, Constructor _ | FConstructor _, Arrow _ ->
      false

let rec align ?(parameters_rev = []) fast_ty (ty : Type.t) =
  let go () =
    match (fast_ty, ty) with
    | FArrow {left= fast_left; right= fast_right; _}, Arrow _ ->
        align ~parameters_rev:(fast_left :: parameters_rev) fast_right ty
    | _ ->
        []
  in
  if aligned fast_ty ty then (List.rev parameters_rev, fast_ty) :: go ()
  else go ()

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

let rec fast_unify cxt fast_ty (ty : Type.t) =
  match (fast_ty, ty) with
  | FId ({contents= ty_opt} as ty_opt_ref), ty -> (
    match ty_opt with
    | Some ty' ->
        Type_unification.unify cxt ty' ty
    | None ->
        ty_opt_ref := Some ty ;
        cxt )
  | FArrow f_a, Arrow a ->
      let cxt = fast_unify cxt f_a.left a.left in
      fast_unify cxt f_a.right a.right
  | FConstructor f_c, Constructor c ->
      if String.(f_c.name = c.name) then
        List.fold2_exn f_c.parameters c.parameters ~init:cxt ~f:fast_unify
      else
        raise
          (Type_unification.UnificationFailure
             (Format.sprintf "constructors are not the same: %s <> %s" f_c.name
                c.name ) )
  | FArrow {polymorphic= Some ty'; _}, Id i
  | FConstructor {polymorphic= Some ty'; _}, Id i ->
      Type_context.bind i ty' cxt
  | FConstructor {parameters= []; polymorphic= None; _}, _ ->
      failwith "fast_unify: parameterless constructor is not monomorphic"
  | FArrow {left= f_l; right= f_r; polymorphic= None}, Id i ->
      let l, cxt = Type_context.make_id cxt in
      let r, cxt = Type_context.make_id cxt in
      let a : Type.arr = {left= l; right= r; polymorphic= true} in
      let cxt = Type_context.bind i (Arrow a) cxt in
      let cxt = fast_unify cxt f_l l in
      fast_unify cxt f_r l
  | FConstructor {name; parameters= fast_parameters; polymorphic= None}, Id i ->
      let parameters, cxt =
        Type_context.make_ids (List.length fast_parameters) cxt
      in
      let c : Type.cons = {name; parameters; polymorphic= true} in
      let cxt = Type_context.bind i (Constructor c) cxt in
      List.fold2_exn fast_parameters parameters ~init:cxt ~f:fast_unify
  | FArrow _, Constructor _ | FConstructor _, Arrow _ ->
      raise
        (Type_unification.UnificationFailure
           "constructor does not unify with arrow" )

let unifier ty =
  let fast_ty, types = of_type ty in
  fun cxt req ->
    let decompositions = align fast_ty req in
    let fail_msg =
      Format.sprintf "%s does not unify with %s" (Type.to_string req)
        (Type.to_string ty)
    in
    if List.is_empty decompositions then
      raise (Type_unification.UnificationFailure fail_msg) ;
    let unifications =
      List.fold decompositions ~init:[]
        ~f:(fun unifications (parameters_fast_ty, terminal_fast_ty) ->
          try
            let cxt' = fast_unify cxt terminal_fast_ty req in
            let next_id = cxt'.next_id in
            let next_id_ref = ref next_id in
            let parameters =
              List.map parameters_fast_ty ~f:(to_type next_id_ref)
            in
            let cxt'' =
              snd @@ Type_context.make_ids (!next_id_ref - next_id) cxt'
            in
            Array.iter types ~f:(fun ty_opt -> ty_opt := None) ;
            (cxt'', parameters) :: unifications
          with Type_unification.UnificationFailure _ -> unifications )
    in
    if List.is_empty unifications then
      raise (Type_unification.UnificationFailure fail_msg)
    else unifications
