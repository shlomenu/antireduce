open Core

let compression_verbosity = ref 0

let collect_data = ref false

let grammar_induction_score ~primitive_size_penalty ~dsl_size_penalty
    (dsl : Dsl.t) log_likelihood_of_frontier =
  log_likelihood_of_frontier
  -. primitive_size_penalty
     *. ( Float.of_int @@ List.reduce_exn ~f:( + )
        @@ List.map dsl.library
             ~f:(Fn.compose Program.size Dsl_entry.to_primitive) )
  -. (dsl_size_penalty *. (Float.of_int @@ List.length dsl.library))

exception EtaExpandFailure

let eta_expansion req p =
  let cxt_ref = ref Type_context.empty in
  let eta_expand p req =
    if Type.is_arrow req then
      Some
        (Program.Abstraction (Apply (Program.shift_free_variables 1 p, Index 0)))
    else None
  in
  let rec go req env : Program.t -> Program.t = function
    | Abstraction b when Type.is_arrow req ->
        Abstraction
          (go (Type.right_of_arrow req) (Type.left_of_arrow req :: env) b)
    | Abstraction _ ->
        raise EtaExpandFailure
    | p -> (
      match eta_expand p req with
      | Some p' ->
          go req env p'
      | None ->
          let f, xs = Program.unpack_application p in
          let f_ty =
            match f with
            | Index i ->
                Type_context.apply' cxt_ref @@ List.nth_exn env i
            | Primitive {ty; _} | Invented {ty; _} ->
                Type_context.instantiate' cxt_ref ty
            | Abstraction _ | Apply _ ->
                failwith
                  "eta_expansion: input is not fully beta-reduced: this could \
                   occur because of a flaw in the program synthesis procedure \
                   or because the input has undergone inverse beta-reduction \
                   and the internal abstractions introduced have not been \
                   properly marked as representing new (invented) primitives"
          in
          Type_unification.unify' cxt_ref req @@ Type.terminal f_ty ;
          let f_ty = Type_context.apply' cxt_ref f_ty in
          let xs_ty = Type.parameters f_ty in
          if List.length xs <> List.length xs_ty then raise EtaExpandFailure
          else
            List.map2_exn xs xs_ty ~f:(fun x x_ty ->
                go (Type_context.apply' cxt_ref x_ty) env x )
            |> List.fold ~init:f ~f:(fun f' x -> Apply (f', x)) )
  in
  let p' = go req [] p in
  assert (
    Type.equal
      (Type.to_canonical @@ Program.closed_inference p)
      (Type.to_canonical @@ Program.closed_inference p') ) ;
  p'

let normalize_invention name i =
  let m =
    Program.free_variables i
    |> List.dedup_and_sort ~compare:( - )
    |> List.mapi ~f:(fun k v -> (v, k))
  in
  let rec go d : Program.t -> Program.t = function
    | Index j when j < d ->
        Index j
    | Index j ->
        Index (d + List.Assoc.find_exn ~equal m (j - d))
    | Abstraction b ->
        Abstraction (go (d + 1) b)
    | Apply (f, x) ->
        Apply (go d f, go d x)
    | (Primitive _ | Invented _) as p ->
        p
  in
  Program.invention name
  @@ List.fold_right m ~init:(go 0 i) ~f:(fun _ e -> Program.Abstraction e)

let refactor invention_name i req e =
  let m =
    Program.free_variables i
    |> List.dedup_and_sort ~compare:( - )
    |> List.mapi ~f:(fun k v -> (k, v))
  in
  let applied_invention =
    List.range 0 (List.length m)
    |> List.fold ~init:(normalize_invention invention_name i) ~f:(fun e j ->
           Apply (e, Index (List.Assoc.find_exn ~equal m j)) )
  in
  let rec go : Program.t -> Program.t = function
    | e when Program.equal e i ->
        applied_invention
    | Apply (f, x) ->
        Apply (go f, go x)
    | Abstraction b ->
        Abstraction (go b)
    | e ->
        e
  in
  try
    let e' = eta_expansion req @@ go e in
    let e_reduced = Program.beta_normal_form ~reduce_invented:true e in
    let e_reduced' = Program.beta_normal_form ~reduce_invented:true e' in
    if not (Program.equal e_reduced e_reduced') then
      failwith
      @@ Format.sprintf
           "program semantics were modified by use of new primitive:\n\
            %s\n\
            \t-/->\n\
            %s\n"
           (Program.to_string e_reduced)
           (Program.to_string e_reduced') ;
    e'
  with Type_unification.UnificationFailure _ ->
    if !compression_verbosity >= 4 then (
      Printf.eprintf "WARNING: rewriting with invention gave ill typed term.\n" ;
      Printf.eprintf "Original:\t\t%s\n" (Program.to_string e) ;
      Printf.eprintf "Original:\t\t%s\n"
        (Program.to_string @@ Program.beta_normal_form ~reduce_invented:true e) ;
      Printf.eprintf "Rewritten:\t\t%s\n" (Program.to_string @@ go e) ;
      Printf.eprintf "Rewritten:\t\t%s\n"
        ( Program.to_string
        @@ Program.beta_normal_form ~reduce_invented:true
        @@ go e ) ;
      Printf.eprintf
        "Going to proceed as if the rewrite had failed - but look into this \
         because it could be a bug.\n" ;
      Util.flush_all () ) ;
    let normal_original = Program.beta_normal_form e ~reduce_invented:true in
    let normal_rewritten =
      Program.beta_normal_form ~reduce_invented:true @@ go e
    in
    assert (Program.equal normal_original normal_rewritten) ;
    raise EtaExpandFailure

let nontrivial e =
  let indices = ref [] in
  let duplicated_indices = ref 0 in
  let primitives = ref 0 in
  let rec go d : Program.t -> unit = function
    | Index i ->
        let i = i - d in
        if List.mem ~equal !indices i then incr duplicated_indices
        else indices := i :: !indices
    | Apply (f, x) ->
        go d f ; go d x
    | Abstraction b ->
        go (d + 1) b
    | Primitive _ | Invented _ ->
        incr primitives
  in
  go 0 e ;
  !primitives > 1 || (!primitives = 1 && !duplicated_indices > 0)

let incorporate_programs ~n_beta_inversions ~inlining version_tbl ps =
  Util.time_it
    (Format.sprintf "calculated %d-step beta inversions.. \n" n_beta_inversions)
    (fun () ->
      List.map ps ~f:(fun p ->
          if !compression_verbosity >= 3 then
            Format.eprintf "%d-step inversion.. %s\n" n_beta_inversions
              (Program.to_string p) ;
          Version_table.n_step_inversion ~inlining version_tbl
            ~n:n_beta_inversions
          @@ Version_table.incorporate version_tbl p ) )

let extract_inventions invention_name version_tbl cost_tbl spaces =
  Util.time_it "proposed refactorings.." (fun () ->
      Version_table.reachable_versions version_tbl spaces
      |> List.concat_map ~f:(fun s ->
             List.dedup_and_sort ~compare:( - )
             @@ snd
             @@ Version_and_cost_table.minimum_cost_inhabitants cost_tbl s )
      |> List.find_all_dups ~compare:( - )
      |> List.filter ~f:(fun s ->
             let p = Version_table.extract_program version_tbl s in
             try
               ignore (normalize_invention invention_name p : Program.t) ;
               nontrivial p
             with Type_unification.UnificationFailure _ -> false ) )

let expand_dsl invention_name dsl invention =
  let primitive = normalize_invention invention_name invention in
  let primitives = Dsl.to_primitives dsl in
  if List.mem ~equal:Program.equal primitives primitive then None
  else
    Some
      ( primitive
      , Dsl.of_primitives_dedup dsl.state_type (primitive :: primitives) )

let rewrite_programs invention_name cost_tbl version_tbl req s_inv inv (s_p, p)
    =
  if !compression_verbosity >= 3 then
    Format.eprintf "rewriting program.. %s\n" (Program.to_string p) ;
  let p' =
    try
      Util.value_exn
      @@ Cost_table.minimal_inhabitant cost_tbl ~given:(Some s_inv) s_p
    with _ ->
      failwith
      @@ Format.sprintf "could not find minimal inhabitant of %s\n"
      @@ Program.to_string
      @@ Version_table.extract_program version_tbl s_p
  in
  try refactor invention_name inv req p' with EtaExpandFailure -> p

let compression_step ~invention_name_prefix ~inlining ~n_beta_inversions
    ~beam_size ~n_invention_sizes ~n_exactly_scored ~primitive_size_penalty
    ~dsl_size_penalty ~request ~(dsl : Dsl.t) ~frontier =
  let tbl = Version_table.create () in
  let cost_and_version_tbl = Version_and_cost_table.empty tbl in
  let frontier_spaces =
    incorporate_programs ~n_beta_inversions ~inlining tbl frontier
  in
  let invention_name =
    match Dsl_entry.to_primitive @@ List.hd_exn dsl.library with
    | Invented {name; _} ->
        let splits = String.split name ~on:'_' in
        let init, last = List.split_n splits (List.length splits - 1) in
        String.concat init ~sep:"_"
        ^ "_" ^ Int.to_string @@ ( + ) 1 @@ Int.of_string @@ List.hd_exn last
    | _ ->
        invention_name_prefix ^ "_0"
  in
  let invention_spaces =
    extract_inventions invention_name tbl cost_and_version_tbl frontier_spaces
  in
  Printf.eprintf "Got %d candidates.\n" (List.length invention_spaces) ;
  if List.is_empty invention_spaces then None
  else
    let cost_ranked_inventions =
      Util.time_it "ranked candidates." (fun () ->
          Beam_search.beams_and_costs ~cost_and_version_tbl ~beam_size
            ~inventions:invention_spaces frontier_spaces )
      |> List.filter_map ~f:(fun (cost, i) ->
             let invention = Version_table.extract_program tbl i in
             expand_dsl invention_name dsl invention
             |> Option.map ~f:(fun (invented_primitive, expanded_dsl) ->
                    ( (float_of_int @@ Program.size invention, cost)
                    , (i, invention, invented_primitive, expanded_dsl) ) ) )
    in
    let size_limited_cost_ranked_inventions =
      match n_invention_sizes with
      | Some n_invention_sizes ->
          let size_and_cost_ranked_inventions =
            List.sort cost_ranked_inventions ~compare:(fun (k_1, _) (k_2, _) ->
                Util.FloatPair.compare k_1 k_2 )
          in
          let unique_invention_sizes =
            List.remove_consecutive_duplicates ~equal:Float.equal
            @@ List.map size_and_cost_ranked_inventions ~f:(Fn.compose fst fst)
          in
          ( match
              List.nth unique_invention_sizes (max 0 (n_invention_sizes - 1))
            with
          | Some max_invention_size ->
              List.take_while size_and_cost_ranked_inventions
                ~f:(fun ((size, _), _) -> Float.(size <= max_invention_size))
          | None ->
              size_and_cost_ranked_inventions )
          |> List.sort ~compare:(fun ((_, c_1), _) ((_, c_2), _) ->
                 Float.compare c_1 c_2 )
      | None ->
          cost_ranked_inventions
    in
    let ( best_invention_score
        , best_invention_size
        , best_rewritten_frontier
        , best_invented_primitive
        , best_expanded_dsl ) =
      List.take size_limited_cost_ranked_inventions n_exactly_scored
      |> List.fold ~init:None
           ~f:(fun
                best
                ((size, cost), (i, invention, invented_primitive, expanded_dsl))
              ->
             let cost_tbl = Cost_table.empty tbl in
             let rewritten_frontier =
               List.zip_exn frontier_spaces frontier
               |> List.map
                    ~f:
                      (rewrite_programs invention_name cost_tbl tbl request i
                         invention )
             in
             let reweighted_expanded_dsl, log_likelihood_of_frontier =
               Factorization.inside_outside expanded_dsl request
                 rewritten_frontier
             in
             let score =
               grammar_induction_score ~primitive_size_penalty ~dsl_size_penalty
                 reweighted_expanded_dsl log_likelihood_of_frontier
             in
             if !compression_verbosity > 1 then
               Printf.eprintf
                 "Invention: (%s : %s)\n\
                  Approximate description length after refactor: %f\n\
                  Score: %f\n"
                 (Program.to_string invented_primitive)
                 (Type.to_string @@ Program.closed_inference invented_primitive)
                 cost score ;
             let result =
               ( score
               , size
               , rewritten_frontier
               , invented_primitive
               , reweighted_expanded_dsl )
             in
             Option.value_map best ~default:(Some result)
               ~f:(fun (top_score, _, _, _, _) ->
                 if Float.(score > top_score) then Some result else best ) )
      |> Util.value_exn
    in
    let _, initial_log_likelihood_of_frontier =
      Factorization.inside_outside dsl request frontier
    in
    let initial_score =
      grammar_induction_score ~primitive_size_penalty ~dsl_size_penalty dsl
        initial_log_likelihood_of_frontier
    in
    Printf.eprintf
      "Best candidate changes score from %f to %f (difference: %f) w/ new \
       primitive of size %d and mass %d\n\
       \t(%s : %s)\n\n"
      initial_score best_invention_score
      (best_invention_score -. initial_score)
      (int_of_float best_invention_size)
      (Program.mass best_invented_primitive)
      (Program.to_string best_invented_primitive)
      ( Type.to_string @@ Type.to_canonical
      @@ Program.closed_inference best_invented_primitive ) ;
    if Float.(best_invention_score > initial_score) then
      Some (best_expanded_dsl, best_rewritten_frontier)
    else None

let export_compression_checkpoint ~invention_name_prefix ~n_beta_inversions
    ~beam_size ~n_invention_sizes ~n_exactly_scored ~primitive_size_penalty
    ~dsl_size_penalty ~dsl ~frontier =
  let ts = Time.to_filename_string ~zone:Time.Zone.utc @@ Time.now () in
  let filename = Printf.sprintf "compression_messages/%s" ts in
  let j : Yojson.Safe.t =
    `Assoc
      [ ("dsl", Dsl.yojson_of_t dsl)
      ; ("n_invention_sizes", yojson_of_option yojson_of_int n_invention_sizes)
      ; ("n_exactly_scored", yojson_of_int n_exactly_scored)
      ; ("primitive_size_penalty", yojson_of_float primitive_size_penalty)
      ; ("dsl_size_penalty", yojson_of_float dsl_size_penalty)
      ; ("beam_size", yojson_of_int beam_size)
      ; ("n_beta_inversions", yojson_of_int n_beta_inversions)
      ; ("verbose", yojson_of_bool true)
      ; ("invention_name_prefix", yojson_of_string invention_name_prefix)
      ; ( "frontier"
        , `List
            (List.map frontier ~f:(fun p ->
                 yojson_of_string (Program.to_string p) ) ) ) ]
  in
  Yojson.Safe.to_file filename j ;
  Printf.eprintf "Exported compression checkpoint to %s\n" filename

let illustrate_primitive_usage primitive programs =
  let illustrations =
    List.filter_map programs ~f:(fun p ->
        if List.mem ~equal:Program.equal (Program.subexpressions p) primitive
        then Some p
        else None )
  in
  Printf.eprintf "New primitive is used %d times: \n"
    (List.length illustrations) ;
  List.iter illustrations ~f:(fun p ->
      Printf.eprintf "  %s\n" (Program.to_string p) )

let find_new_primitive dsl dsl' =
  match
    List.filter
      ~f:
        (Fn.compose not
           (List.mem ~equal:Program.equal (Dsl.to_primitives dsl)) )
    @@ Dsl.to_primitives dsl'
  with
  | [primitive] ->
      primitive
  | [] ->
      failwith "no new primitive after single successful compression iteration"
  | _ ->
      failwith
        "multiple new primitives after single successful compression iteration"

let compress ~invention_name_prefix ~inlining ~n_beta_inversions ~beam_size
    ~n_invention_sizes ~n_exactly_scored ~primitive_size_penalty
    ~dsl_size_penalty ~iterations ~request ~dsl ~frontier =
  assert (n_exactly_scored > 0) ;
  let rec go ~iterations dsl frontier =
    if iterations > 0 then (
      match
        Util.time_it "Completed one step of memory consolidation" (fun () ->
            compression_step ~invention_name_prefix ~inlining ~n_beta_inversions
              ~beam_size ~n_invention_sizes ~n_exactly_scored
              ~primitive_size_penalty ~dsl_size_penalty ~request ~dsl ~frontier )
      with
      | None ->
          (dsl, frontier)
      | Some (dsl', frontier') ->
          if !compression_verbosity >= 1 then
            illustrate_primitive_usage (find_new_primitive dsl dsl') frontier' ;
          if !compression_verbosity >= 4 && iterations > 1 then
            export_compression_checkpoint ~invention_name_prefix
              ~n_beta_inversions ~beam_size ~n_invention_sizes ~n_exactly_scored
              ~primitive_size_penalty ~dsl_size_penalty ~dsl:dsl'
              ~frontier:frontier' ;
          Util.flush_all () ;
          go ~iterations:(iterations - 1) dsl' frontier' )
    else (dsl, frontier)
  in
  let dsl', frontier' =
    Util.time_it "completed ocaml compression" (fun () ->
        go ~iterations dsl frontier )
  in
  (dsl', frontier')
