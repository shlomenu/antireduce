open Core
open Type
open Program
open Grammar
open Versions
module T = Domainslib.Task
module C = Domainslib.Chan

let verbose_compression = ref false

let collect_data = ref false

let grammar_induction_score ~primitive_size_penalty ~grammar_size_penalty
    request transforms gmr =
  let log_prob =
    let n_transforms = Float.of_int @@ List.length transforms in
    let factorizations = List.map transforms ~f:(factorize gmr request) in
    Util.fold1 ( +. )
    @@ List.map factorizations ~f:(fun fact ->
           log (1. /. n_transforms) +. likelihood_of_factorization gmr fact )
  in
  let production_size = function
    | Primitive _ ->
        1
    | Invented (_, b) ->
        size_of_program @@ strip_abstractions b
    | _ ->
        failwith
          "grammar contains entry which is not base or invented primitive"
  in
  log_prob
  -. (primitive_size_penalty *. (Float.of_int @@ List.length gmr.library))
  -. grammar_size_penalty
     *. ( Float.of_int @@ List.reduce_exn ~f:( + )
        @@ List.map gmr.library ~f:(fun ent ->
               production_size @@ primitive_of_entry ent ) )

exception EtaExpandFailure

let eta_expansion req p =
  let cxt_ref = ref empty_type_context in
  let eta_expand p req =
    if is_arrow req then
      Some (Abstraction (Apply (shift_free_variables 1 p, Index 0)))
    else None
  in
  let rec go req env = function
    | Abstraction b when is_arrow req ->
        Abstraction (go (right_of_arrow req) (left_of_arrow req :: env) b)
    | Abstraction _ ->
        raise EtaExpandFailure
    | p -> (
      match eta_expand p req with
      | Some p' ->
          go req env p'
      | None ->
          let f, xs = unpack_application p in
          let f_ty =
            match f with
            | Index i ->
                apply_context_ref cxt_ref @@ List.nth_exn env i
            | Primitive {ty; _} | Invented (ty, _) ->
                instantiate_type_ref cxt_ref ty
            | Abstraction _ | Apply _ ->
                failwith "eta_expansion"
          in
          unify_ref cxt_ref req @@ terminal_of_type f_ty ;
          let f_ty = apply_context_ref cxt_ref f_ty in
          let xs_ty = parameters_of_type f_ty in
          if List.length xs <> List.length xs_ty then raise EtaExpandFailure
          else
            List.map2_exn xs xs_ty ~f:(fun x x_ty ->
                go (apply_context_ref cxt_ref x_ty) env x )
            |> List.fold ~init:f ~f:(fun f' x -> Apply (f', x)) )
  in
  let p' = go req [] p in
  assert (
    equal_dc_type
      (canonical_type @@ closed_inference p)
      (canonical_type @@ closed_inference p') ) ;
  p'

let normalize_invention i =
  let m =
    free_variables i
    |> List.dedup_and_sort ~compare:( - )
    |> List.mapi ~f:(fun k v -> (v, k))
  in
  let rec go d = function
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
  invention @@ List.fold_right m ~init:(go 0 i) ~f:(fun _ e -> Abstraction e)

let rewrite_with_invention i =
  let m =
    free_variables i
    |> List.dedup_and_sort ~compare:( - )
    |> List.mapi ~f:(fun k v -> (k, v))
  in
  let applied_invention =
    List.range 0 (List.length m)
    |> List.fold ~init:(normalize_invention i) ~f:(fun e j ->
           Apply (e, Index (List.Assoc.find_exn ~equal m j)) )
  in
  let rec go e =
    if equal_program e i then applied_invention
    else
      match e with
      | Apply (f, x) ->
          Apply (go f, go x)
      | Abstraction b ->
          Abstraction (go b)
      | Index _ | Primitive _ | Invented _ ->
          e
  in
  fun req e ->
    try
      let e' = eta_expansion req @@ go e in
      assert (
        equal_program
          (beta_normal_form ~reduce_invented:true e)
          (beta_normal_form ~reduce_invented:true e') ) ;
      e'
    with UnificationFailure ->
      if !verbose_compression then (
        Printf.eprintf
          "WARNING: rewriting with invention gave ill typed term.\n" ;
        Printf.eprintf "Original:\t\t%s\n" (string_of_program e) ;
        Printf.eprintf "Original:\t\t%s\n"
          (string_of_program @@ beta_normal_form ~reduce_invented:true e) ;
        Printf.eprintf "Rewritten:\t\t%s\n" (string_of_program @@ go e) ;
        Printf.eprintf "Rewritten:\t\t%s\n"
          (string_of_program @@ beta_normal_form ~reduce_invented:true @@ go e) ;
        Printf.eprintf
          "Going to proceed as if the rewrite had failed - but look into this \
           because it could be a bug.\n" ;
        Util.flush_all () ) ;
      let normal_original = beta_normal_form e ~reduce_invented:true in
      let normal_rewritten = beta_normal_form ~reduce_invented:true @@ go e in
      assert (equal_program normal_original normal_rewritten) ;
      raise EtaExpandFailure

let nontrivial e =
  let indices = ref [] in
  let duplicated_indices = ref 0 in
  let primitives = ref 0 in
  let rec go d = function
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

let compression_step ~inlining ~grammar_size_penalty ~primitive_size_penalty
    ?(n_beta_inversions = 3) ~beam_size ~top_i request gmr transforms =
  let score =
    grammar_induction_score ~primitive_size_penalty ~grammar_size_penalty
      request
  in
  let tbl = new_version_tbl () in
  let cost_tbl = empty_cost_tbl tbl in
  let transform_versions =
    Util.time_it "calculated version spaces" (fun () ->
        List.map transforms ~f:(fun p ->
            Util.time_it
              (Format.sprintf "n-step inversion.. %s\n" (string_of_program p))
              (fun () ->
                n_step_inversion ~inlining tbl ~n:n_beta_inversions
                @@ incorporate tbl p ) ) )
  in
  let refactorings =
    Util.time_it "proposed refactorings.." (fun () ->
        reachable_versions tbl transform_versions
        |> List.concat_map ~f:(fun i ->
               List.dedup_and_sort ~compare:( - )
               @@ snd
               @@ minimum_cost_inhabitants cost_tbl i )
        |> List.find_all_dups ~compare:( - )
        |> List.filter ~f:(fun refactoring ->
               let refactoring = List.hd_exn (extract tbl refactoring) in
               try
                 ignore (normalize_invention refactoring : program) ;
                 nontrivial refactoring
               with UnificationFailure -> false ) )
  in
  Printf.eprintf "Got %d candidates.\n" (List.length refactorings) ;
  match refactorings with
  | [] ->
      None
  | _ ->
      let ranked_refactorings =
        Util.time_it "beamed version space" (fun () ->
            beams_and_costs ~cost_tbl ~beam_size refactorings transform_versions
            |> Fn.flip List.take top_i )
      in
      Format.eprintf "List.length ranked_refactorings: %d\n"
      @@ List.length ranked_refactorings ;
      Util.flush_all () ;
      let initial_score = score transforms gmr in
      Format.eprintf "Initial score: %f\n" initial_score ;
      let[@warning "-27"] best_score, gmr', transforms', best_i =
        Util.time_it (Printf.sprintf "Evaluated top-%d refactorings" top_i)
          (fun () ->
            Util.minimum_by ~compare:Float.compare ~f:(fun (s, _, _, _) -> -.s)
            @@ List.mapi ranked_refactorings ~f:(fun k (cost, i) ->
                   let new_primitive =
                     normalize_invention @@ Util.singleton_list @@ extract tbl i
                   in
                   Format.eprintf "normalized_invention: %s"
                   @@ string_of_program new_primitive ;
                   let score, gmr', transforms' =
                     try
                       Gc.compact () ;
                       let primitives = primitives_of_grammar gmr in
                       if List.mem ~equal:equal_program primitives new_primitive
                       then raise DuplicatePrimitive ;
                       let gmr' =
                         deduplicated_grammar_of_primitives
                           (new_primitive :: primitives)
                       in
                       let rewriter = rewrite_with_invention new_primitive in
                       let new_cost_tbl = empty_cheap_cost_tbl tbl in
                       let transforms' =
                         List.zip_exn transform_versions transforms
                         |> List.mapi ~f:(fun l (j, p) ->
                                Util.time_it
                                  (Format.sprintf
                                     "rewriting program %d with new primitive %d\n"
                                     l k ) (fun () ->
                                    let p' =
                                      try
                                        Util.value_exn
                                        @@ minimal_inhabitant new_cost_tbl
                                             ~given:(Some i) j
                                      with _ ->
                                        Format.eprintf
                                          "could not find minimal inhabitant \
                                           of %s\n"
                                        @@ string_of_program
                                        @@ Util.singleton_list @@ extract tbl j ;
                                        failwith "failed"
                                    in
                                    try rewriter request p'
                                    with EtaExpandFailure -> p ) )
                       in
                       (score transforms' gmr', gmr', transforms')
                     with UnificationFailure | DuplicatePrimitive ->
                       (Float.neg_infinity, gmr, transforms)
                   in
                   if !verbose_compression then (
                     Printf.eprintf
                       "Invention %s : %s\n\
                        Discrete score %f\n\
                        \tContinuous score %f\n\n"
                       (string_of_program new_primitive)
                       (string_of_dc_type @@ closed_inference new_primitive)
                       cost score ;
                     Util.flush_all () ) ;
                   (score, gmr', transforms', i) ) )
      in
      let new_primitive = List.hd_exn @@ primitives_of_grammar gmr' in
      Printf.eprintf
        "Improved score to %f (d_score=%f) w/ new primitive\n\t%s : %s\n"
        best_score
        (best_score -. initial_score)
        (string_of_program new_primitive)
        (string_of_dc_type @@ canonical_type @@ closed_inference new_primitive) ;
      Util.flush_all () ;
      Some (gmr', transforms')

let export_compression_checkpoint ~n_cores ~grammar_size_penalty
    ~primitive_size_penalty ?(n_beta_inversions = 3) ~beam_size ~top_i gmr
    transforms =
  let ts = Time.to_filename_string ~zone:Time.Zone.utc @@ Time.now () in
  let filename = Printf.sprintf "compression_messages/%s" ts in
  let j : Yojson.Safe.t =
    `Assoc
      [ ("DSL", yojson_of_grammar gmr)
      ; ("top_i", `Int top_i)
      ; ("beam_size", `Int beam_size)
      ; ("n_beta_inversions", `Int n_beta_inversions)
      ; ("grammar_size_penalty", `Float grammar_size_penalty)
      ; ("verbose", `Bool true)
      ; ("CPUs", `Int n_cores)
      ; ("primitive_size_penalty", `Float primitive_size_penalty)
      ; ( "transforms"
        , `List (List.map transforms ~f:(fun p -> `String (string_of_program p)))
        ) ]
  in
  Yojson.Safe.to_file filename j ;
  Printf.eprintf "Exported compression checkpoint to %s\n" filename

let compress ?(n_cores = 1) ~grammar_size_penalty ~inlining
    ~primitive_size_penalty ?(n_beta_inversions = 3) ~beam_size ~top_i
    ~iterations request gmr transforms =
  let find_new_primitive gmr gmr' =
    let primitives = primitives_of_grammar gmr in
    let primitives' = primitives_of_grammar gmr' in
    let f = Fn.compose not (List.mem ~equal:equal_program primitives) in
    Util.singleton_list @@ List.filter primitives' ~f
  in
  let illustrate_new_primitive prim transforms =
    let illustrations =
      List.filter_map transforms ~f:(fun p ->
          if List.mem ~equal:equal_program (subexpressions p) prim then Some p
          else None )
    in
    Printf.eprintf
      "New primitive is used %d times in the best programs in each of the \
       frontiers.\n"
      (List.length illustrations) ;
    Printf.eprintf "Here is where it is used:\n" ;
    List.iter illustrations ~f:(fun p ->
        Printf.eprintf "  %s\n" (string_of_program p) )
  in
  let rec go ~iterations gmr frontiers =
    if iterations < 1 then (
      Printf.eprintf "Exiting ocaml compression because of iteration bound.\n" ;
      (gmr, frontiers) )
    else
      match
        Util.time_it "Completed one step of memory consolidation" (fun () ->
            compression_step ~inlining ~grammar_size_penalty
              ~primitive_size_penalty ~n_beta_inversions ~beam_size ~top_i
              request gmr transforms )
      with
      | None ->
          (gmr, frontiers)
      | Some (gmr', frontiers') ->
          illustrate_new_primitive (find_new_primitive gmr gmr') frontiers' ;
          if !verbose_compression && iterations > 1 then
            export_compression_checkpoint ~n_cores ~grammar_size_penalty
              ~primitive_size_penalty ~n_beta_inversions ~beam_size ~top_i gmr'
              frontiers' ;
          Util.flush_all () ;
          go ~iterations:(iterations - 1) gmr' frontiers'
  in
  Util.time_it "completed ocaml compression" (fun () ->
      go ~iterations gmr transforms )
