open Core

type t =
  { function_cost: (float * int list) option Array_list.t
  ; argument_cost: (float * int list) option Array_list.t
  ; parent: Version_table.t }

let empty (tbl : Version_table.t) =
  { function_cost= Array_list.create ()
  ; argument_cost= Array_list.create ()
  ; parent= tbl }

let rec minimum_cost_inhabitants ?(given = None) ?(can_be_lambda = true)
    (cost_tbl : t) i =
  let cache =
    if can_be_lambda then cost_tbl.argument_cost else cost_tbl.function_cost
  in
  Array_list.ensure_length cache (i + 1) None ;
  match Array_list.get cache i with
  | Some c_inds ->
      c_inds
  | None ->
      let c, inds =
        match given with
        | Some invention
          when Version_table.intersecting cost_tbl.parent invention i ->
            (1., [invention])
        | _ -> (
          match Version_table.version_of_int cost_tbl.parent i with
          | Universe | Void ->
              failwith "minimum_cost_inhabitants"
          | IndexSpace _ | TerminalSpace _ ->
              (1., [i])
          | Union u ->
              let children =
                List.map u
                  ~f:(minimum_cost_inhabitants ~given ~can_be_lambda cost_tbl)
              in
              let c =
                List.reduce_exn ~f:Float.min @@ List.map children ~f:fst
              in
              if Util.is_invalid c then (c, [])
              else
                let children =
                  List.concat_map ~f:snd
                  @@ List.filter children ~f:(fun (cost, _) ->
                         Float.(cost = c) )
                in
                (c, children)
          | AbstractionSpace b when can_be_lambda ->
              let c, children =
                minimum_cost_inhabitants ~given ~can_be_lambda cost_tbl b
              in
              let c = c +. Version_table.epsilon_cost in
              let children =
                List.map children
                  ~f:(Version_table.version_of_abstraction cost_tbl.parent)
              in
              (c, children)
          | AbstractionSpace _ ->
              (Float.infinity, [])
          | ApplySpace (f, x) ->
              let c_f, children_f =
                minimum_cost_inhabitants ~given ~can_be_lambda:false cost_tbl f
              in
              let c_x, children_x =
                minimum_cost_inhabitants ~given ~can_be_lambda:true cost_tbl x
              in
              if Util.is_invalid c_f || Util.is_invalid c_x then
                (Float.infinity, [])
              else
                ( c_f +. c_x +. Version_table.epsilon_cost
                , List.concat_map children_f ~f:(fun f' ->
                      List.map children_x ~f:(fun x' ->
                          Version_table.version_of_apply cost_tbl.parent f' x' ) )
                ) )
      in
      let c_inds = (c, List.dedup_and_sort inds ~compare:( - )) in
      Array_list.set cache i (Some c_inds) ;
      c_inds
