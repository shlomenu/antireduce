open Core

module Derivation_min_heap = Containers.Heap.Make_from_compare (struct
  type t = Derivation.t

  let compare (a : t) (b : t) = -Float.compare a.log_likelihood b.log_likelihood
end)

type t =
  { heap: Derivation_min_heap.t Map.M(Type).t
  ; succ: Derivation.t Map.M(Derivation).t Map.M(Type).t
  ; seen: Set.M(Derivation).t Map.M(Type).t }

let initialize pcfg : t =
  let cache =
    Map.keys (Pcfg.rules pcfg)
    |> List.fold
         ~init:
           { heap= Map.empty (module Type)
           ; succ= Map.empty (module Type)
           ; seen= Map.empty (module Type) }
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
            let nonterminals =
              List.map prod.nonterminals ~f:(fun nt ->
                  Map.find_exn pcfg.max_prob nt )
            in
            let deriv =
              Derivation.Fields.create ~terminal:prod.terminal ~nonterminals
                ~nonterminal:nt
                ~log_likelihood:
                  (List.fold nonterminals ~init:prod.log_likelihood
                     ~f:(fun ll_tot leaf -> ll_tot +. leaf.log_likelihood) )
            in
            (Derivation_min_heap.add nt_heap deriv, Set.add nt_seen deriv) )
      in
      { cache' with
        heap= Map.set cache'.heap ~key:nt ~data:nt_heap
      ; seen= Map.set cache'.seen ~key:nt ~data:nt_seen } )

let rec query deriv_cur cache =
  let nt = Derivation.nonterminal deriv_cur in
  let nt_succ = Map.find_exn cache.succ nt in
  match Map.find nt_succ deriv_cur with
  | Some deriv_next ->
      (deriv_next, cache)
  | None ->
      let nt_heap = Map.find_exn cache.heap nt in
      let nt_heap', deriv_next = Derivation_min_heap.take_exn nt_heap in
      ( deriv_next
      , snd
        @@ List.fold deriv_next.nonterminals
             ~init:
               ( ([], List.drop deriv_next.nonterminals 1)
               , { cache with
                   heap= Map.set cache.heap ~key:nt ~data:nt_heap'
                 ; succ=
                     Map.set cache.succ ~key:nt
                       ~data:
                         (Map.add_exn nt_succ ~key:deriv_cur ~data:deriv_next)
                 } )
             ~f:(fun ((pre, post), cache') leaf ->
               let leaf_next, cache'' = query leaf cache' in
               ( (leaf :: pre, List.drop post 1)
               , let deriv_next' =
                   { deriv_next with
                     nonterminals= List.rev_append (leaf_next :: pre) post
                   ; log_likelihood=
                       deriv_next.log_likelihood -. leaf.log_likelihood
                       +. leaf_next.log_likelihood }
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
