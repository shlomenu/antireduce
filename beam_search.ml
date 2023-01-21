open Core

type t =
  { unrefactored_func_cost: float
  ; unrefactored_arg_cost: float
  ; mutable refactored_func_cost: (int, float) Hashtbl.t
  ; mutable refactored_arg_cost: (int, float) Hashtbl.t }

let limit_beam ~beam_size b =
  let limit beam =
    if Hashtbl.length beam > beam_size then
      Hashtbl.to_alist beam
      |> List.sort ~compare:(fun (_, c_1) (_, c_2) -> Float.compare c_1 c_2)
      |> (Fn.flip List.take) beam_size
      |> Hashtbl.of_alist_exn (module Int)
    else beam
  in
  b.refactored_func_cost <- limit b.refactored_func_cost ;
  b.refactored_arg_cost <- limit b.refactored_arg_cost

let relax tbl ~key ~data =
  Hashtbl.change tbl key
    ~f:
      (Option.value_map ~default:(Some data) ~f:(fun v ->
           if Float.(v > data) then Some data else None ) )

let func_cost b i =
  Hashtbl.find b.refactored_func_cost i
  |> Option.value_map ~f:Fn.id ~default:b.unrefactored_func_cost

let arg_cost b i =
  Hashtbl.find b.refactored_arg_cost i
  |> Option.value_map ~f:Fn.id ~default:b.unrefactored_arg_cost

let inventions_costs tbl inventions =
  let costs = Hashtbl.create (module Int) in
  List.iter inventions ~f:(fun invention ->
      let cost =
        Float.of_int @@ List.length
        @@ List.dedup_and_sort ~compare:( - )
        @@ Program.free_variables
        @@ Version_table.extract_program tbl invention
      in
      Hashtbl.set costs ~key:invention ~data:(1. +. cost) ) ;
  costs

let beams ~(cost_and_version_tbl : Version_and_cost_table.t) ~beam_size
    inventions frontier =
  let costs = inventions_costs cost_and_version_tbl.parent inventions in
  let inventions = Hash_set.Poly.of_list inventions in
  let cache = Array_list.create () in
  let rec go i =
    Array_list.ensure_length cache (i + 1) None ;
    match Array_list.get cache i with
    | Some beam ->
        beam
    | None ->
        let unrefactored_arg_cost, inhabitants =
          Version_and_cost_table.minimum_cost_inhabitants ~can_be_lambda:true
            cost_and_version_tbl i
        in
        let unrefactored_func_cost, _ =
          Version_and_cost_table.minimum_cost_inhabitants ~can_be_lambda:false
            cost_and_version_tbl i
        in
        let beam =
          { unrefactored_arg_cost
          ; unrefactored_func_cost
          ; refactored_func_cost= Hashtbl.create (module Int)
          ; refactored_arg_cost= Hashtbl.create (module Int) }
        in
        List.filter inhabitants ~f:(Hash_set.mem inventions)
        |> List.iter ~f:(fun invention ->
               let cost = Hashtbl.find_exn costs invention in
               Hashtbl.set beam.refactored_func_cost ~key:invention ~data:cost ;
               Hashtbl.set beam.refactored_arg_cost ~key:invention ~data:cost ) ;
        ( match Version_table.version_of_int cost_and_version_tbl.parent i with
        | AbstractionSpace b ->
            let child = go b in
            Hashtbl.iteri child.refactored_arg_cost ~f:(fun ~key ~data ->
                relax beam.refactored_arg_cost ~key
                  ~data:(data +. Version_table.epsilon_cost) )
        | ApplySpace (f, x) ->
            let beam_f = go f in
            let beam_x = go x in
            let refactored_with =
              Hashtbl.keys beam_f.refactored_func_cost
              @ Hashtbl.keys beam_x.refactored_arg_cost
            in
            List.iter refactored_with ~f:(fun invention ->
                let c =
                  Version_table.epsilon_cost +. func_cost beam_f invention
                  +. arg_cost beam_x invention
                in
                relax beam.refactored_func_cost ~key:invention ~data:c ;
                relax beam.refactored_arg_cost ~key:invention ~data:c )
        | Union u ->
            List.iter u ~f:(fun v ->
                let child = go v in
                Hashtbl.iteri child.refactored_func_cost ~f:(fun ~key ~data ->
                    relax beam.refactored_func_cost ~key ~data ) ;
                Hashtbl.iteri child.refactored_arg_cost ~f:(fun ~key ~data ->
                    relax beam.refactored_arg_cost ~key ~data ) )
        | IndexSpace _ | Universe | Void | TerminalSpace _ ->
            () ) ;
        limit_beam ~beam_size beam ;
        Array_list.set cache i (Some beam) ;
        beam
  in
  List.iter frontier ~f:(fun i -> ignore (go i : t)) ;
  cache

let beam_costs ~cost_and_version_tbl ~beam_size inventions frontier =
  let cache = beams ~cost_and_version_tbl ~beam_size inventions frontier in
  let beams =
    List.map frontier ~f:(fun i -> Util.value_exn @@ Array_list.get cache i)
  in
  List.map inventions ~f:(fun invention ->
      List.reduce_exn ~f:( +. )
      @@ List.map beams ~f:(fun beam ->
             Float.min (arg_cost beam invention) (func_cost beam invention) ) )

let beams_and_costs ~cost_and_version_tbl ~beam_size ~inventions frontier =
  let costs = beam_costs ~cost_and_version_tbl ~beam_size inventions frontier in
  List.zip_exn costs inventions
  |> List.sort ~compare:(fun (s_1, _) (s_2, _) -> Float.compare s_1 s_2)
