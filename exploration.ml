open Core
module S = Yojson.Safe
module SU = Yojson.Safe.Util

let unikey_representations_tbl ~representations_dir ~primary_key_of_yojson
    ~parse primary_key_modl =
  Caml.Sys.readdir representations_dir
  |> Array.fold ~init:(Hashtbl.create primary_key_modl) ~f:(fun repr filename ->
         let j = S.from_file @@ Filename.concat representations_dir filename in
         SU.member "primary_key" j |> primary_key_of_yojson
         |> Hashtbl.update repr ~f:(function
              | None ->
                  ( None
                  , Some (parse @@ SU.to_string @@ SU.member "program" j)
                  , SU.member "output" j )
              | Some _ ->
                  failwith
                    "unikey_representations_tbl: multiple data share a primary \
                     key without a secondary key to differentiate them" ) ;
         repr )

let multikey_representations_tbl ~representations_dir ~primary_key_of_yojson
    ~secondary_key_of_yojson ~parse key_modl =
  Caml.Sys.readdir representations_dir
  |> Array.fold ~init:(Hashtbl.create key_modl) ~f:(fun repr filename ->
         let j = S.from_file @@ Filename.concat representations_dir filename in
         let data' =
           ( None
           , Some (parse @@ SU.to_string @@ SU.member "program" j)
           , secondary_key_of_yojson @@ SU.member "secondary_key" j
           , SU.member "output" j )
         in
         SU.member "primary_key" j |> primary_key_of_yojson
         |> Hashtbl.update repr ~f:(function
              | None ->
                  [data']
              | Some data ->
                  data' :: data ) ;
         repr )

let unikey_store_if_hit ~apply_to_state ~dsl ~evaluate ~eval_timeout ~attempts
    ~retrieve_result ~nontrivial ~primary_key_of_output ~yojson_of_output
    representations p =
  let p_applied = apply_to_state p in
  Arg_typed_program.of_program (Dsl.state_type dsl) p_applied
  |> evaluate ~timeout:eval_timeout ~attempts p_applied
  |> Option.map ~f:retrieve_result
  |> Option.bind ~f:(fun o -> if nontrivial o then Some o else None)
  |> Option.value_map ~default:() ~f:(fun o ->
         Hashtbl.update representations (primary_key_of_output o) ~f:(function
           | None ->
               (Some p, None, yojson_of_output o)
           | Some (None, None, _) ->
               failwith "unikey_store_if_hit: vacuous entry"
           | Some (None, (Some prev_p as prev_best), o) ->
               let cur_best =
                 if Program.mass p < Program.mass prev_p then Some p else None
               in
               (cur_best, prev_best, o)
           | Some ((Some cur_p as cur_best), prev_best, o) ->
               let cur_best =
                 if Program.mass p < Program.mass cur_p then Some p
                 else cur_best
               in
               (cur_best, prev_best, o) ) )

let multikey_store_if_hit ~apply_to_state ~dsl ~evaluate ~eval_timeout ~attempts
    ~retrieve_result ~nontrivial ~keys_of_output ~yojson_of_output
    ~equal_secondary_key representations p =
  let p_applied = apply_to_state p in
  Arg_typed_program.of_program (Dsl.state_type dsl) p_applied
  |> evaluate ~timeout:eval_timeout ~attempts p_applied
  |> Option.map ~f:retrieve_result
  |> Option.bind ~f:(fun o -> if nontrivial o then Some o else None)
  |> Option.value_map ~default:() ~f:(fun o ->
         let primary_key, secondary_key = keys_of_output o in
         Hashtbl.update representations primary_key ~f:(function
           | None ->
               [(Some p, None, secondary_key, yojson_of_output o)]
           | Some [] ->
               failwith "multikey_store_if_hit: unpopulated table entry"
           | Some hits -> (
             match
               List.fold hits ~init:(false, []) ~f:(fun (found, hits') hit ->
                   if found then (found, hit :: hits')
                   else
                     match hit with
                     | None, None, _, _ ->
                         failwith "multikep_store_if_hit: vacuous entry"
                     | ( None
                       , (Some prev_p as prev_best)
                       , prev_secondary_key
                       , prev_o ) ->
                         if equal_secondary_key secondary_key prev_secondary_key
                         then
                           let cur_best, secondary_key', o' =
                             if Program.mass p < Program.mass prev_p then
                               (Some p, secondary_key, yojson_of_output o)
                             else (None, prev_secondary_key, prev_o)
                           in
                           ( true
                           , (cur_best, prev_best, secondary_key', o') :: hits'
                           )
                         else (found, hit :: hits')
                     | ( (Some cur_p as cur_best)
                       , prev_best
                       , cur_secondary_key
                       , cur_o ) ->
                         if equal_secondary_key secondary_key cur_secondary_key
                         then
                           let cur_best, secondary_key', o' =
                             if Program.mass p < Program.mass cur_p then
                               (Some p, secondary_key, yojson_of_output o)
                             else (cur_best, cur_secondary_key, cur_o)
                           in
                           ( true
                           , (cur_best, prev_best, secondary_key', o') :: hits'
                           )
                         else (found, hit :: hits') )
             with
             | false, hits' ->
                 (Some p, None, secondary_key, yojson_of_output o)
                 :: List.rev hits'
             | true, hits' ->
                 List.rev hits' ) ) )

let unikey_replacements ~representations_dir ~yojson_of_primary_key =
  Hashtbl.fold ~init:(0, 0, [])
    ~f:(fun ~key ~data ((n_new, n_replaced, replacements) as cur) ->
      match data with
      | None, None, _ ->
          failwith "unikey_replacements: unpopulated entry"
      | None, Some _, _ ->
          cur
      | Some cur_p, prev_best, o_save ->
          let path_of = Frontier.repr_path representations_dir in
          let cur_path = path_of cur_p in
          let n_new', n_replaced', replacements' =
            match prev_best with
            | Some prev_p ->
                let prev_path = path_of prev_p in
                Caml.Sys.remove prev_path ;
                ( n_new
                , n_replaced + 1
                , (Filename.basename prev_path, Filename.basename cur_path)
                  :: replacements )
            | None ->
                (n_new + 1, n_replaced, replacements)
          in
          S.to_file cur_path
          @@ `Assoc
               [ ("program", yojson_of_string @@ Program.to_string cur_p)
               ; ( "stitch_program"
                 , yojson_of_string @@ Program.to_string ~format:`Stitch cur_p
                 )
               ; ("size", yojson_of_int (Program.size cur_p))
               ; ( "mass"
                 , yojson_of_int
                     ( Program.mass
                     @@ Program.beta_normal_form ~reduce_invented:true cur_p )
                 )
               ; ("output", o_save)
               ; ("primary_key", yojson_of_primary_key key) ] ;
          (n_new', n_replaced', replacements') )

let multikey_replacements ~representations_dir ~yojson_of_primary_key
    ~yojson_of_secondary_key representations =
  Hashtbl.to_alist representations
  |> List.concat_map ~f:(fun (primary_key, secondary_key_list) ->
         List.map secondary_key_list
           ~f:(fun (cur_best, prev_best, secondary_key, output) ->
             (cur_best, prev_best, primary_key, secondary_key, output) ) )
  |> List.fold ~init:(0, 0, [])
       ~f:(fun ((n_new, n_replaced, replacements) as cur) -> function
       | None, None, _, _, _ ->
           failwith "multikey_replacements: unpopulated entry"
       | None, Some _, _, _, _ ->
           cur
       | Some cur_p, prev_best, primary_key, secondary_key, o_save ->
           let path_of = Frontier.repr_path representations_dir in
           let cur_path = path_of cur_p in
           let n_new', n_replaced', replacements' =
             match prev_best with
             | Some prev_p ->
                 let prev_path = path_of prev_p in
                 Caml.Sys.remove prev_path ;
                 ( n_new
                 , n_replaced + 1
                 , (Filename.basename prev_path, Filename.basename cur_path)
                   :: replacements )
             | None ->
                 (n_new + 1, n_replaced, replacements)
           in
           S.to_file cur_path
           @@ `Assoc
                [ ("program", yojson_of_string @@ Program.to_string cur_p)
                ; ( "stitch_program"
                  , yojson_of_string @@ Program.to_string ~format:`Stitch cur_p
                  )
                ; ("size", yojson_of_int (Program.size cur_p))
                ; ( "mass"
                  , yojson_of_int
                      ( Program.mass
                      @@ Program.beta_normal_form ~reduce_invented:true cur_p )
                  )
                ; ("output", o_save)
                ; ("primary_key", yojson_of_primary_key primary_key)
                ; ("secondary_key", yojson_of_secondary_key secondary_key) ] ;
           (n_new', n_replaced', replacements') )

let enumerate_until_timeout ~timeout ~size_limit ~process_program deriv cache =
  let start_ll = Derivation.log_likelihood deriv in
  let start_program = Derivation.to_program deriv in
  let end_time = Core_unix.time () +. timeout in
  let rec go ?(count = 0) deriv_cur p_cur cache' =
    if Float.(Core_unix.time () < end_time) then (
      let deriv_next, cache'' = Heap_search.query deriv_cur cache' in
      let p_next = Derivation.to_program deriv_next in
      if Float.(deriv_next.log_likelihood > deriv_cur.log_likelihood) then
        failwith
        @@ Format.sprintf
             "explore: heap search returned programs in nondecreasing order of \
              likelihood: P(\n\
              %s\n\
              )\t>\n\
              P(\n\
              %s\n\
              )"
             (Program.to_string p_next) (Program.to_string p_cur) ;
      if Program.size p_next > size_limit then
        go ~count deriv_next p_next cache''
      else (
        process_program p_next ;
        go ~count:(count + 1) deriv_next p_next cache'' ) )
    else (count, deriv_cur.log_likelihood, cache')
  in
  let count, finish_ll, cache' = go deriv start_program cache in
  (count, start_ll, finish_ll, cache')

let unikey_explore ~exploration_timeout ~program_size_limit ~eval_timeout
    ~attempts ~dsl ~representations_dir ~apply_to_state ~evaluate
    ~retrieve_result ~nontrivial ~parse ~request ~yojson_of_output
    ~primary_key_of_output ~yojson_of_primary_key ~primary_key_of_yojson
    primary_key_modl =
  if
    not
      ( Type.equal request
      @@ Type.arrow (Dsl.state_type dsl) (Dsl.state_type dsl) )
  then
    failwith
      "unikey_explore: requested type must be of the form: dsl.state_type -> \
       dsl.state_type" ;
  let representations =
    unikey_representations_tbl ~representations_dir ~primary_key_of_yojson
      ~parse primary_key_modl
  in
  let initial_deriv =
    Derivation.Fields.create
      ~terminal:(Primitive {name= "UNK"; ty= request})
      ~nonterminals:[] ~nonterminal:request ~log_likelihood:0.
  in
  let n_enumerated, _, max_ll, _ =
    enumerate_until_timeout ~timeout:exploration_timeout
      ~size_limit:program_size_limit
      ~process_program:
        (unikey_store_if_hit ~apply_to_state ~dsl ~evaluate ~eval_timeout
           ~attempts ~retrieve_result ~nontrivial ~primary_key_of_output
           ~yojson_of_output representations )
      initial_deriv
    @@ Heap_search.initialize @@ Pcfg.of_dsl request dsl
  in
  let n_new, n_replaced, replacements =
    unikey_replacements ~representations_dir ~yojson_of_primary_key
      representations
  in
  (n_new, n_replaced, replacements, n_enumerated, max_ll)

let multikey_explore ~exploration_timeout ~program_size_limit ~eval_timeout
    ~attempts ~dsl ~representations_dir ~apply_to_state ~evaluate
    ~retrieve_result ~nontrivial ~parse ~request ~yojson_of_output
    ~keys_of_output ~yojson_of_primary_key ~primary_key_of_yojson
    ~yojson_of_secondary_key ~secondary_key_of_yojson ~equal_secondary_key
    primary_key_modl =
  if
    not
      ( Type.equal request
      @@ Type.arrow (Dsl.state_type dsl) (Dsl.state_type dsl) )
  then
    failwith
      "multikey_explore: requested type must be of the form: dsl.state_type -> \
       dsl.state_type" ;
  let representations =
    multikey_representations_tbl ~representations_dir ~primary_key_of_yojson
      ~secondary_key_of_yojson ~parse primary_key_modl
  in
  let initial_deriv =
    Derivation.Fields.create
      ~terminal:(Primitive {name= "UNK"; ty= request})
      ~nonterminals:[] ~nonterminal:request ~log_likelihood:0.
  in
  let n_enumerated, _, max_ll, _ =
    enumerate_until_timeout ~timeout:exploration_timeout
      ~size_limit:program_size_limit
      ~process_program:
        (multikey_store_if_hit ~apply_to_state ~dsl ~evaluate ~eval_timeout
           ~attempts ~retrieve_result ~nontrivial ~keys_of_output
           ~yojson_of_output ~equal_secondary_key representations )
      initial_deriv
    @@ Heap_search.initialize @@ Pcfg.of_dsl request dsl
  in
  let n_new, n_replaced, replacements =
    multikey_replacements ~representations_dir ~yojson_of_primary_key
      ~yojson_of_secondary_key representations
  in
  (n_new, n_replaced, replacements, n_enumerated, max_ll)
