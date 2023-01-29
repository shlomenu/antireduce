open Core

module T = struct
  type unseen =
    { terminal: Program.t
    ; nonterminals: t list
    ; nonterminal: Type.t
    ; log_likelihood: float }

  and t = Unseen of unseen | Seen of Type.t
  [@@deriving equal, compare, sexp_of, fields]
end

include T
include Comparator.Make (T)

let rec unify (partial_deriv, cxt) =
  match partial_deriv with
  | Unseen ({nonterminal; _} as unseen) ->
      Unseen
        { unseen with
          nonterminal= snd @@ Type_context.apply cxt nonterminal
        ; nonterminals=
            List.map unseen.nonterminals ~f:(fun pd -> unify (pd, cxt)) }
  | Seen ty ->
      Seen (snd @@ Type_context.apply cxt ty)

let to_type = function
  | Unseen {nonterminal; _} ->
      nonterminal
  | Seen nonterminal ->
      nonterminal

let rec to_productions = function
  | Unseen {nonterminal; terminal; nonterminals; log_likelihood} ->
      ( nonterminal
      , Production.Fields.create ~terminal
          ~nonterminals:(List.map nonterminals ~f:to_type)
          ~log_likelihood )
      :: List.concat_map nonterminals ~f:to_productions
  | Seen _ ->
      []

module Transition = struct
  module T = struct
    type t = Program.t * int * Program.t [@@deriving equal, compare, sexp_of]
  end

  include T
  include Comparator.Make (T)
end

let rec find ?(type_size_limit = 100)
    ?(transitions = Set.empty (module Transition))
    ?(seen_nts = Set.empty (module Structural_type))
    ?(completed_nts = Set.empty (module Structural_type))
    ?(trans : Transition.t option = None) dsl cxt req =
  if (not (Set.is_empty seen_nts)) && Set.mem completed_nts (Some cxt, req) then
    [(Seen req, cxt)]
  else if
    Type.size req > type_size_limit
    || Set.mem seen_nts (Some cxt, req)
    || Option.value_map trans ~default:false ~f:(fun trans ->
           Set.mem transitions trans )
  then []
  else
    let seen_nts' =
      Set.add seen_nts @@ Structural_type.of_contextual_type cxt req
    in
    Dsl_unification.expressions dsl [] req cxt
    |> List.sort ~compare:(fun u_1 u_2 ->
           Int.compare (List.length u_1.parameters) (List.length u_2.parameters) )
    |> List.concat_map ~f:(fun unified ->
           let transitions' =
             Option.value_map trans ~default:transitions
               ~f:(Set.add transitions)
           in
           let trans' i =
             match trans with
             | Some (_, _, parent) ->
                 Some (parent, i, unified.expr)
             | None ->
                 Some (Primitive {name= "UNK"; ty= req}, i, unified.expr)
           in
           List.fold unified.parameters
             ~init:[([], unified.context, 0)]
             ~f:(fun params_derivs param ->
               List.concat_map params_derivs
                 ~f:(fun (params_deriv, cxt', position) ->
                   let cxt'', param' = Type_context.apply cxt' param in
                   find ~transitions:transitions' ~seen_nts:seen_nts'
                     ~completed_nts ~trans:(trans' position) dsl cxt'' param'
                   |> List.map ~f:(fun (param_deriv, cxt''') ->
                          (param_deriv :: params_deriv, cxt''', position + 1) ) )
               )
           |> List.map ~f:(fun (params_deriv_rev, cxt', _) ->
                  ( Unseen
                      (Fields_of_unseen.create ~terminal:unified.expr
                         ~nonterminals:(List.rev params_deriv_rev)
                         ~nonterminal:req ~log_likelihood:unified.log_likelihood )
                  , cxt' ) ) )
