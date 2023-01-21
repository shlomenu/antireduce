open Core

type t = {next_id: int; types: Type.t Map.M(Int).t}

let empty = {next_id= 0; types= Map.empty (module Int)}

let make_id ({next_id; types} as cxt) : Type.t * t =
  assert (Option.is_none @@ Map.find types next_id) ;
  (Id next_id, {cxt with next_id= next_id + 1})

let rec make_ids (n : int) ?(ids = []) (cxt : t) : Type.t list * t =
  if n <= 0 then (List.rev ids, cxt)
  else
    let ty, cxt = make_id cxt in
    let ids = ty :: ids in
    make_ids (n - 1) ~ids cxt

let bind i ty cxt : t = {cxt with types= Map.set cxt.types ~key:i ~data:ty}

let lookup cxt i =
  assert (i < cxt.next_id) ;
  Map.find cxt.types i

let rec apply cxt : Type.t -> t * Type.t = function
  | ty when not (Type.is_polymorphic ty) ->
      (cxt, ty)
  | Id j as ty -> (
    match lookup cxt j with
    | Some ty_other ->
        let cxt, ty' = apply cxt ty_other in
        let cxt = if Type.equal ty ty' then cxt else bind j ty' cxt in
        (cxt, ty')
    | None ->
        (cxt, ty) )
  | Constructor con ->
      let f parameter (cxt, parameters) =
        let cxt, parameter = apply cxt parameter in
        (cxt, parameter :: parameters)
      in
      let cxt, parameters = List.fold_right con.parameters ~init:(cxt, []) ~f in
      (cxt, Type.kind con.name parameters)
  | Arrow {left; right; _} ->
      let cxt, right = apply cxt right in
      let cxt, left = apply cxt left in
      (cxt, Type.arrow left right)

let compose_substitutions cxt_a cxt_b =
  let next_id = max cxt_a.next_id cxt_b.next_id in
  let types =
    List.range ~start:`inclusive ~stop:`exclusive 0 (next_id - 1)
    |> List.filter_map ~f:(fun i ->
           let ty : Type.t = Id i in
           let ty = if i < cxt_a.next_id then snd @@ apply cxt_a ty else ty in
           let ty = if i < cxt_b.next_id then snd @@ apply cxt_b ty else ty in
           if Type.equal ty (Id i) then None else Some (i, ty) )
    |> Map.of_alist_exn (module Int)
  in
  {next_id; types}

let apply' cxt_ref ty =
  let cxt', ty' = apply !cxt_ref ty in
  cxt_ref := cxt' ;
  ty'

let instantiate cxt (ty : Type.t) =
  let types = ref [] in
  let cxt_ref = ref cxt in
  let rec instantiate : Type.t -> Type.t = function
    | ty_j when not (Type.is_polymorphic ty_j) ->
        ty_j
    | Id i -> (
      try List.Assoc.find_exn ~equal !types i
      with Not_found_s _ ->
        let ty, cxt' = make_id !cxt_ref in
        cxt_ref := cxt' ;
        types := (i, ty) :: !types ;
        ty )
    | Arrow {left; right; _} ->
        Type.arrow (instantiate left) (instantiate right)
    | Constructor {name; parameters; _} ->
        Type.kind name @@ List.map parameters ~f:instantiate
  in
  let ty_inst = instantiate ty in
  (!cxt_ref, ty_inst)

let instantiate' cxt_ref ty =
  let cxt', ty' = instantiate !cxt_ref ty in
  cxt_ref := cxt' ;
  ty'

let rec pad_type cxt n ty =
  if n <= 0 then (cxt, ty)
  else
    let p, cxt = make_id cxt in
    let cxt, ps = pad_type cxt (n - 1) ty in
    (cxt, Type.(p @> ps))
