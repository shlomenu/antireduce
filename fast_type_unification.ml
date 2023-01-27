open Core

type t =
  { fast_ty: Fast_type.t
  ; types: Type.t option ref array
  ; unify: Type_context.t -> Type.t -> (Type_context.t * Type.t list) list }

let rec aligned (fast_ty : Fast_type.t) (ty : Type.t) =
  match (fast_ty, ty) with
  | FArrow {right= fast_right; _}, Arrow {right; _} ->
      aligned fast_right right
  | _, Id _ | FId _, _ | FConstructor _, Constructor _ ->
      true
  | FArrow _, Constructor _ | FConstructor _, Arrow _ ->
      false

let rec align ?(parameters_rev = []) (fast_ty : Fast_type.t) (ty : Type.t) =
  let go () =
    match (fast_ty, ty) with
    | FArrow {left= fast_left; right= fast_right; _}, Arrow _ ->
        align ~parameters_rev:(fast_left :: parameters_rev) fast_right ty
    | _ ->
        []
  in
  if aligned fast_ty ty then (List.rev parameters_rev, fast_ty) :: go ()
  else go ()

let rec unify cxt (fast_ty : Fast_type.t) (ty : Type.t) =
  match (fast_ty, ty) with
  | FId ({contents= ty_opt} as ty_opt_ref), ty -> (
    match ty_opt with
    | Some ty' ->
        Type_unification.unify cxt ty' ty
    | None ->
        ty_opt_ref := Some ty ;
        cxt )
  | FArrow f_a, Arrow a ->
      let cxt = unify cxt f_a.left a.left in
      unify cxt f_a.right a.right
  | FConstructor f_c, Constructor c ->
      if String.(f_c.name = c.name) then
        List.fold2_exn f_c.parameters c.parameters ~init:cxt ~f:unify
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
      let cxt = unify cxt f_l l in
      unify cxt f_r l
  | FConstructor {name; parameters= fast_parameters; polymorphic= None}, Id i ->
      let parameters, cxt =
        Type_context.make_ids (List.length fast_parameters) cxt
      in
      let c : Type.cons = {name; parameters; polymorphic= true} in
      let cxt = Type_context.bind i (Constructor c) cxt in
      List.fold2_exn fast_parameters parameters ~init:cxt ~f:unify
  | FArrow _, Constructor _ | FConstructor _, Arrow _ ->
      raise
        (Type_unification.UnificationFailure
           "constructor does not unify with arrow" )

let of_type ty =
  let fast_ty, types = Fast_type.of_type ty in
  { fast_ty
  ; types
  ; unify=
      (fun cxt req ->
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
                let cxt' = unify cxt terminal_fast_ty req in
                let next_id = cxt'.next_id in
                let next_id_ref = ref next_id in
                let parameters =
                  List.map parameters_fast_ty ~f:(Fast_type.to_type next_id_ref)
                in
                let cxt'' =
                  snd @@ Type_context.make_ids (!next_id_ref - next_id) cxt'
                in
                Array.iter types ~f:(fun ty_opt -> ty_opt := None) ;
                (cxt'', parameters) :: unifications
              with Type_unification.UnificationFailure _ ->
                Array.iter types ~f:(fun ty_opt -> ty_opt := None) ;
                unifications )
        in
        if List.is_empty unifications then
          raise (Type_unification.UnificationFailure fail_msg)
        else unifications ) }
