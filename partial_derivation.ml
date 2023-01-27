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

let rec find ?(type_size_limit = 100) ?(seen_nts = []) ?(completed_nts = []) dsl
    cxt req =
  if
    (not (List.is_empty seen_nts))
    && List.mem completed_nts req ~equal:Type.equal
  then [(Seen req, cxt)]
  else if
    Type.size req > type_size_limit
    || List.mem seen_nts req ~equal:(fun req' nt ->
           try
             ignore (Type_unification.unify cxt req' nt : Type_context.t) ;
             true
           with Type_unification.UnificationFailure _ -> false )
  then []
  else
    let seen_nts' = req :: seen_nts in
    Dsl_unification.expressions dsl [] req cxt
    |> List.sort ~compare:(fun u_1 u_2 ->
           Int.compare (List.length u_1.parameters) (List.length u_2.parameters) )
    |> List.concat_map ~f:(fun unified ->
           List.fold unified.parameters
             ~init:[([], unified.context)]
             ~f:(fun params_derivs param ->
               List.concat_map params_derivs ~f:(fun (params_deriv, cxt') ->
                   let cxt'', param' = Type_context.apply cxt' param in
                   find ~seen_nts:seen_nts' ~completed_nts dsl cxt'' param'
                   |> List.map ~f:(fun (param_deriv, cxt''') ->
                          (param_deriv :: params_deriv, cxt''') ) ) )
           |> List.map ~f:(fun (params_deriv_rev, cxt') ->
                  ( Unseen
                      (Fields_of_unseen.create ~terminal:unified.expr
                         ~nonterminals:(List.rev params_deriv_rev)
                         ~nonterminal:req ~log_likelihood:unified.log_likelihood )
                  , cxt' ) ) )
