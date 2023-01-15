open Core
open Type
open Program
open Dsl
module S = Yojson.Safe
module SU = Yojson.Safe.Util

type production =
  {terminal: program; parameters: dc_type list; log_likelihood: float}

type derivation =
  { root: program
  ; leaves: derivation list
  ; nonterminal: dc_type
  ; log_likelihood: float }
[@@deriving equal, compare, sexp_of]

module Derivation = struct
  type t = derivation [@@deriving equal, compare, sexp_of]

  include Comparator.Make (struct
    type t = derivation [@@deriving equal, compare, sexp_of]
  end)
end

let rec program_of_derivation {root; leaves; _} =
  List.fold leaves ~init:root ~f:(fun f x_tree ->
      Apply (f, program_of_derivation x_tree) )

type pcfg =
  { start: dc_type
  ; rules: (DcType.t, production list, DcType.comparator_witness) Map.t
  ; max_prob: (DcType.t, derivation, DcType.comparator_witness) Map.t }

let rec enumerate_rules dsl cxt rules req =
  if not (Map.mem rules req) then
    unifying_expressions dsl [] req cxt
    |> List.sort ~compare:(fun u_1 u_2 ->
           -Float.compare u_1.log_likelihood u_2.log_likelihood )
    |> List.fold ~init:(Map.add_exn rules ~key:req ~data:[])
         ~f:(fun rules' unified ->
           let rules'' =
             List.fold unified.parameters ~init:rules'
               ~f:(enumerate_rules dsl unified.context)
           in
           let prod =
             { terminal= unified.expr
             ; parameters= unified.parameters
             ; log_likelihood= unified.log_likelihood }
           in
           Map.update rules'' req
             ~f:
               (Option.value_map ~default:[prod] ~f:(fun prods ->
                    prod :: prods ) ) )
  else rules

let rules_of_dsl start dsl =
  enumerate_rules dsl empty_type_context (Map.empty (module DcType)) start

let max_prob_parameterless rules =
  Map.fold rules
    ~init:(Map.empty (module DcType))
    ~f:(fun ~key:nt ~data:prods max_prob' ->
      List.filter prods ~f:(fun prod -> List.is_empty prod.parameters)
      |> List.sort ~compare:(fun pr_1 pr_2 ->
             -Float.compare pr_1.log_likelihood pr_2.log_likelihood )
      |> List.hd
      |> Option.value_map ~default:max_prob' ~f:(fun max_prod ->
             Map.add_exn max_prob' ~key:nt
               ~data:
                 { root= max_prod.terminal
                 ; leaves= []
                 ; nonterminal= nt
                 ; log_likelihood= max_prod.log_likelihood } ) )

let rec max_prob_rest rules max_prob =
  let unevaluated = Set.diff (Map.key_set rules) (Map.key_set max_prob) in
  if not (Set.is_empty unevaluated) then
    max_prob_rest rules
    @@ Set.fold unevaluated ~init:max_prob ~f:(fun max_prob' nt ->
           Map.find_exn rules nt
           |> List.fold_until
                ~init:
                  { root= Primitive {name= "UNK"; ty= nt}
                  ; leaves= []
                  ; nonterminal= nt
                  ; log_likelihood= Float.neg_infinity }
                ~finish:Option.return
                ~f:(fun deriv prod ->
                  let leaves =
                    List.filter_map prod.parameters ~f:(Map.find max_prob')
                  in
                  if List.length leaves = List.length prod.parameters then
                    let deriv' =
                      { root= prod.terminal
                      ; leaves
                      ; nonterminal= nt
                      ; log_likelihood=
                          List.fold leaves ~init:prod.log_likelihood
                            ~f:(fun ll_tot leaf ->
                              ll_tot +. leaf.log_likelihood ) }
                    in
                    Continue
                      ( if Float.(deriv'.log_likelihood > deriv.log_likelihood)
                      then deriv'
                      else deriv )
                  else Stop None )
           |> Option.value_map ~default:max_prob' ~f:(fun max_program ->
                  Map.add_exn max_prob' ~key:nt ~data:max_program ) )
  else max_prob

let max_prob_of_rules rules =
  max_prob_rest rules @@ max_prob_parameterless rules

let pcfg_of_dsl start dsl =
  let rules = rules_of_dsl start dsl in
  {start; rules; max_prob= max_prob_of_rules rules}

module Derivation_min_heap = Containers.Heap.Make_from_compare (struct
  type t = Derivation.t

  let compare (a : t) (b : t) = -Float.compare a.log_likelihood b.log_likelihood
end)

type heap_search_cache =
  { heap: (DcType.t, Derivation_min_heap.t, DcType.comparator_witness) Map.t
  ; succ:
      ( DcType.t
      , (Derivation.t, Derivation.t, Derivation.comparator_witness) Map.t
      , DcType.comparator_witness )
      Map.t
  ; seen:
      ( DcType.t
      , (Derivation.t, Derivation.comparator_witness) Set.t
      , DcType.comparator_witness )
      Map.t }

let initialized_heap_search_cache pcfg : heap_search_cache =
  let cache =
    Map.keys pcfg.rules
    |> List.fold
         ~init:
           { heap= Map.empty (module DcType)
           ; succ= Map.empty (module DcType)
           ; seen= Map.empty (module DcType) }
         ~f:(fun cache' nt ->
           { heap=
               Map.add_exn cache'.heap ~key:nt ~data:Derivation_min_heap.empty
           ; succ=
               Map.add_exn cache'.succ ~key:nt
                 ~data:(Map.empty (module Derivation))
           ; seen=
               Map.add_exn cache'.seen ~key:nt
                 ~data:(Set.empty (module Derivation)) } )
  in
  Map.fold pcfg.rules ~init:cache ~f:(fun ~key:nt ~data:prods cache' ->
      let nt_heap, nt_seen =
        List.fold prods
          ~init:(Map.find_exn cache.heap nt, Map.find_exn cache.seen nt)
          ~f:(fun (nt_heap, nt_seen) prod ->
            let leaves =
              List.map prod.parameters ~f:(fun nt ->
                  Map.find_exn pcfg.max_prob nt )
            in
            let deriv =
              { root= prod.terminal
              ; leaves
              ; nonterminal= nt
              ; log_likelihood=
                  List.fold leaves ~init:prod.log_likelihood
                    ~f:(fun ll_tot leaf -> ll_tot +. leaf.log_likelihood) }
            in
            (Derivation_min_heap.add nt_heap deriv, Set.add nt_seen deriv) )
      in
      { cache' with
        heap= Map.set cache'.heap ~key:nt ~data:nt_heap
      ; seen= Map.set cache'.seen ~key:nt ~data:nt_seen } )

let rec query_heaps deriv_cur cache =
  let nt = deriv_cur.nonterminal in
  let nt_succ = Map.find_exn cache.succ nt in
  match Map.find nt_succ deriv_cur with
  | Some deriv_next ->
      (deriv_next, cache)
  | None ->
      let nt_heap = Map.find_exn cache.heap nt in
      let nt_heap', deriv_next = Derivation_min_heap.take_exn nt_heap in
      ( deriv_next
      , snd
        @@ List.fold deriv_next.leaves
             ~init:
               ( ([], List.drop deriv_next.leaves 1)
               , { cache with
                   heap= Map.set cache.heap ~key:nt ~data:nt_heap'
                 ; succ=
                     Map.set cache.succ ~key:nt
                       ~data:
                         (Map.add_exn nt_succ ~key:deriv_cur ~data:deriv_next)
                 } )
             ~f:(fun ((pre, post), cache') leaf ->
               let leaf_next, cache'' = query_heaps leaf cache' in
               let pre' = leaf_next :: pre in
               ( (pre', List.drop post 1)
               , let deriv_next' =
                   { deriv_next with
                     leaves= List.rev_append pre' post
                   ; log_likelihood=
                       deriv_next.log_likelihood
                       +. (leaf_next.log_likelihood -. leaf.log_likelihood) }
                 in
                 let nt_seen = Map.find_exn cache''.seen nt in
                 if not (Set.mem nt_seen deriv_next') then
                   { cache'' with
                     heap=
                       Map.set cache''.heap ~key:nt
                         ~data:
                           ( Derivation_min_heap.insert deriv_next'
                           @@ Map.find_exn cache''.heap nt )
                   ; seen=
                       Map.set cache''.seen ~key:nt
                         ~data:(Set.add nt_seen deriv_next') }
                 else cache'' ) ) )

let representations_tbl ~representations_dir ~key_of_yojson ~parse key_modl =
  Caml.Sys.readdir representations_dir
  |> Array.fold ~init:(Hashtbl.create key_modl) ~f:(fun repr filename ->
         let j = S.from_file @@ Filename.concat representations_dir filename in
         let key = key_of_yojson @@ SU.member "key" j in
         let p = parse @@ SU.to_string @@ SU.member "program" j in
         Hashtbl.update repr key ~f:(function
           | None ->
               (None, Some p, SU.member "output" j)
           | Some _ ->
               failwith "found multiple programs with the same output key" ) ;
         repr )

let store_if_hit ~apply_to_state ~dsl ~evaluate ~eval_timeout ~attempts
    ~retrieve_result ~nontrivial ~key_of_output ~yojson_of_output
    representations p =
  let p_applied = apply_to_state p in
  generic_expr_of_program dsl.state_type p_applied
  |> evaluate ~timeout:eval_timeout ~attempts p_applied
  |> Option.map ~f:retrieve_result
  |> Option.bind ~f:(fun o -> if nontrivial o then Some o else None)
  |> Option.value_map ~default:() ~f:(fun o ->
         Hashtbl.update representations (key_of_output o) ~f:(function
           | None ->
               (Some p, None, yojson_of_output o)
           | Some (None, None, _) ->
               failwith "unpopulated entry"
           | Some (None, (Some prev_p as prev_best), o) ->
               let cur_best =
                 if mass_of_program p < mass_of_program prev_p then Some p
                 else None
               in
               (cur_best, prev_best, o)
           | Some ((Some cur_p as cur_best), prev_best, o) ->
               let cur_best =
                 if mass_of_program p < mass_of_program cur_p then Some p
                 else cur_best
               in
               (cur_best, prev_best, o) ) )

let replacements ~representations_dir ~yojson_of_key =
  Hashtbl.fold ~init:(0, 0, [])
    ~f:(fun ~key ~data ((n_new, n_replaced, replacements) as cur) ->
      match data with
      | None, None, _ ->
          failwith "unpopulated entry"
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
               [ ("program", yojson_of_string @@ string_of_program cur_p)
               ; ( "stitch_program"
                 , yojson_of_string @@ string_of_program ~format:`Stitch cur_p
                 )
               ; ("size", yojson_of_int (size_of_program cur_p))
               ; ( "mass"
                 , yojson_of_int
                     ( mass_of_program
                     @@ beta_normal_form ~reduce_invented:true cur_p ) )
               ; ("output", o_save)
               ; ("key", yojson_of_key key) ] ;
          (n_new', n_replaced', replacements') )

let enumerate_until_timeout ~timeout ~process_program deriv cache =
  let start_ll = deriv.log_likelihood in
  let start_program = program_of_derivation deriv in
  let end_time = Core_unix.time () +. timeout in
  let rec go ?(count = 0) deriv_cur p_cur cache' =
    if Float.(Core_unix.time () < end_time) then (
      let deriv_next, cache'' = query_heaps deriv_cur cache' in
      let p_next = program_of_derivation deriv_next in
      if Float.(deriv_next.log_likelihood >= deriv_cur.log_likelihood) then
        failwith
        @@ Format.sprintf
             "explore: heap search returned programs in nondecreasing order of \
              likelihood: P(\n\
              %s\n\
              )\t>\n\
              P(\n\
              %s\n\
              )"
             (string_of_program p_next) (string_of_program p_cur) ;
      process_program p_next ;
      go ~count:(count + 1) deriv_next p_next cache'' )
    else (count, deriv_cur.log_likelihood, cache')
  in
  let count, finish_ll, cache' = go deriv start_program cache in
  (count, start_ll, finish_ll, cache')

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir ~apply_to_state ~evaluate ~retrieve_result ~nontrivial
    ~parse ~request ~yojson_of_output ~key_of_output ~yojson_of_key
    ~key_of_yojson key_modl =
  if not (equal_dc_type request @@ arrow dsl.state_type dsl.state_type) then
    failwith
      "explore: requested type must be of the form: dsl.state_type -> \
       dsl.state_type" ;
  let representations =
    representations_tbl ~representations_dir ~key_of_yojson ~parse key_modl
  in
  let initial_deriv =
    { root= Primitive {name= "UNK"; ty= request}
    ; leaves= []
    ; nonterminal= request
    ; log_likelihood= 0. }
  in
  let n_enumerated, _, max_ll, _ =
    enumerate_until_timeout ~timeout:exploration_timeout
      ~process_program:
        (store_if_hit ~apply_to_state ~dsl ~evaluate ~eval_timeout ~attempts
           ~retrieve_result ~nontrivial ~key_of_output ~yojson_of_output
           representations )
      initial_deriv
    @@ initialized_heap_search_cache @@ pcfg_of_dsl request dsl
  in
  let n_new, n_replaced, replacements =
    replacements ~representations_dir ~yojson_of_key representations
  in
  (n_new, n_replaced, replacements, n_enumerated, max_ll)