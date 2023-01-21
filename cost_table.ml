open Core

type t =
  { function_cost: float option Array_list.t
  ; argument_cost: float option Array_list.t
  ; parent: Version_table.t }
[@@deriving fields]

let empty (tbl : Version_table.t) =
  { function_cost= Array_list.create ()
  ; argument_cost= Array_list.create ()
  ; parent= tbl }

let rec minimal_inhabitant_cost ?(memo = None) ?(given = None)
    ?(can_be_lambda = true) cost_tbl i =
  let cache =
    if can_be_lambda then argument_cost cost_tbl else function_cost cost_tbl
  in
  Array_list.ensure_length cache (i + 1) None ;
  match Array_list.get cache i with
  | Some c_inds ->
      c_inds
  | None ->
      let c =
        match given with
        | Some invention
          when Version_table.intersecting ~memo (parent cost_tbl) invention i ->
            1.
        | _ -> (
          match Version_table.version_of_int (parent cost_tbl) i with
          | Universe | Void ->
              failwith "minimal_inhabitant_cost"
          | IndexSpace _ | TerminalSpace _ ->
              1.
          | Union u ->
              List.reduce_exn ~f:Float.min
              @@ List.map u
                   ~f:
                     (minimal_inhabitant_cost ~memo ~given ~can_be_lambda
                        cost_tbl )
          | AbstractionSpace b when can_be_lambda ->
              Version_table.epsilon_cost
              +. minimal_inhabitant_cost ~memo ~given ~can_be_lambda cost_tbl b
          | AbstractionSpace _ ->
              Float.infinity
          | ApplySpace (f, x) ->
              Version_table.epsilon_cost
              +. minimal_inhabitant_cost ~memo ~given ~can_be_lambda:false
                   cost_tbl f
              +. minimal_inhabitant_cost ~memo ~given ~can_be_lambda:true
                   cost_tbl x )
      in
      Array_list.set cache i (Some c) ;
      c

let rec minimal_inhabitant ?(memo = None) ?(given = None)
    ?(can_be_lambda = true) cost_tbl i =
  let c = minimal_inhabitant_cost ~memo ~given ~can_be_lambda cost_tbl i in
  if Util.is_invalid c then None
  else
    Some
      ( match (c, given) with
      | 1., Some invention
        when Version_table.intersecting ~memo (parent cost_tbl) invention i ->
          Version_table.extract_program cost_tbl.parent invention
      | _ -> (
        match Version_table.version_of_int (parent cost_tbl) i with
        | Universe | Void ->
            failwith "minimal_inhabitant"
        | IndexSpace _ | TerminalSpace _ ->
            Version_table.extract_program (parent cost_tbl) i
        | Union u ->
            Util.value_exn
            @@ minimal_inhabitant ~memo ~given ~can_be_lambda cost_tbl
            @@ Util.minimum u ~compare:Float.compare
                 ~key:
                   (minimal_inhabitant_cost ~memo ~given ~can_be_lambda cost_tbl)
        | AbstractionSpace b ->
            Abstraction
              ( Util.value_exn
              @@ minimal_inhabitant ~memo ~given ~can_be_lambda:true cost_tbl b
              )
        | ApplySpace (f, x) ->
            Apply
              ( Util.value_exn
                @@ minimal_inhabitant ~memo ~given ~can_be_lambda:false cost_tbl
                     f
              , Util.value_exn
                @@ minimal_inhabitant ~memo ~given ~can_be_lambda:true cost_tbl
                     x ) ) )
