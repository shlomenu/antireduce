open Core

exception UnificationFailure of string

let rec unify cxt ty_1 ty_2 =
  let cxt, ty_1 = Type_context.apply cxt ty_1 in
  let cxt, ty_2 = Type_context.apply cxt ty_2 in
  if (not (Type.is_polymorphic ty_1)) && not (Type.is_polymorphic ty_2) then
    if Type.equal ty_1 ty_2 then cxt
    else
      raise
        (UnificationFailure
           (Format.sprintf "monomorphic types are not equal: %s <> %s"
              (Type.to_string ty_1) (Type.to_string ty_2) ) )
  else
    match (ty_1, ty_2) with
    | Id j, ty_other | ty_other, Id j ->
        if Type.equal ty_1 ty_2 then cxt
        else if Type.occurs j ty_other then
          raise
            (UnificationFailure
               (Format.sprintf "occurs check did not pass: %s occurs in %s"
                  (Type.to_string (Id j)) (Type.to_string ty_other) ) )
        else Type_context.bind j ty_other cxt
    | Arrow arw_1, Arrow arw_2 ->
        let cxt = unify cxt arw_1.left arw_2.left in
        unify cxt arw_1.right arw_2.right
    | Constructor con_1, Constructor con_2 when String.(con_1.name = con_2.name)
      ->
        List.fold2_exn ~init:cxt con_1.parameters con_2.parameters ~f:unify
    | _ ->
        raise
          (UnificationFailure
             (Format.sprintf "dissimilar structure: %s <> %s"
                (Type.to_string ty_1) (Type.to_string ty_2) ) )

let unify' cxt_ref ty_1 ty_2 = cxt_ref := unify !cxt_ref ty_1 ty_2

let canonical_types tys =
  let next_id_ref = ref 0 in
  let types = ref [] in
  let f = Type.to_canonical ~next_id_ref ~types in
  List.map tys ~f

let unify_many_types tys =
  let ty, cxt = Type_context.make_id Type_context.empty in
  let cxt_ref = ref cxt in
  List.iter tys ~f:(fun ty' ->
      let cxt', ty' = Type_context.instantiate !cxt_ref ty' in
      cxt_ref := unify cxt' ty' ty ) ;
  snd @@ Type_context.apply !cxt_ref ty
