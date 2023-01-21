open Core

type t =
  { expr: Program.t
  ; parameters: Type.t list
  ; context: Type_context.t
  ; log_likelihood: float }
[@@deriving fields]

let environment dsl env req cxt =
  List.filter_mapi env ~f:(fun i ty ->
      let context, ty = Type_context.apply cxt ty in
      let l_ty, l_req = (Type.list_of_arrows ty, Type.list_of_arrows req) in
      let size_ty, size_req = (List.length l_ty, List.length l_req) in
      if size_req > size_ty then None
      else
        let terminal_ty =
          Type.arrows_of_list @@ List.drop l_ty (size_ty - size_req)
        in
        if Type.might_unify terminal_ty req then
          try
            let context = Type_unification.unify context terminal_ty req in
            let context, ty = Type_context.apply context ty in
            let parameters =
              List.take (Type.list_of_arrows ty) (size_ty - size_req)
            in
            Some
              { expr= Index i
              ; parameters
              ; context
              ; log_likelihood= Dsl.var_log_likelihood dsl }
          with Type_unification.UnificationFailure _ -> None
        else None )

let indices dsl env req cxt =
  let unified = environment dsl env req cxt in
  let permitted_unified =
    if Type.equal req dsl.state_type then
      let terminal_indices =
        List.filter_map unified ~f:(fun ent ->
            if List.is_empty ent.parameters then
              Some (Program.int_of_index ent.expr)
            else None )
      in
      if List.is_empty terminal_indices then unified
      else
        let min_terminal_index = List.reduce_exn ~f:min terminal_indices in
        List.filter unified ~f:(fun ent ->
            not
              ( Program.is_index ent.expr
              && List.is_empty ent.parameters
              && Program.int_of_index ent.expr <> min_terminal_index ) )
    else unified
  in
  let tot = log @@ Float.of_int @@ List.length permitted_unified in
  List.map permitted_unified ~f:(fun ent ->
      {ent with log_likelihood= ent.log_likelihood -. tot} )

let primitives dsl req cxt =
  Dsl.library dsl
  |> List.concat_map ~f:(fun ent ->
         try
           ent.unifier cxt req
           |> List.map ~f:(fun (context, parameters) ->
                  { expr= Dsl_entry.to_primitive ent
                  ; parameters
                  ; context
                  ; log_likelihood= ent.log_likelihood } )
         with Type_unification.UnificationFailure _ -> [] )

let expressions dsl env req cxt =
  let unified = indices dsl env req cxt @ primitives dsl req cxt in
  if List.is_empty unified then unified
  else
    let z =
      Util.logsumexp @@ List.map unified ~f:(fun ent -> ent.log_likelihood)
    in
    List.map unified ~f:(fun ent ->
        {ent with log_likelihood= ent.log_likelihood -. z} )
