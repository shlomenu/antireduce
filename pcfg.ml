open Core

module TypeList = struct
  module T = struct
    type t = Type.t list [@@deriving equal, compare, sexp_of]
  end

  include T
  include Comparator.Make (T)
end

type t =
  { start: Type.t
  ; rules: Production.t list Map.M(Type).t
  ; max_prob: Derivation.t Map.M(Type).t }
[@@deriving fields]

let expand_rules ?(type_size_limit = 100) rules dsl req =
  Partial_derivation.find ~type_size_limit ~completed_nts:(Map.keys rules) dsl
    Type_context.empty req
  |> List.concat_map
       ~f:
         (Fn.compose Partial_derivation.to_productions Partial_derivation.unify)
  |> List.fold ~init:(rules, false) ~f:(fun (rules', added') (nt, prod) ->
         match Map.find rules' nt with
         | Some nt_prods ->
             let nt_prods' = Set.add nt_prods prod in
             let added'' = Set.length nt_prods' > Set.length nt_prods in
             (Map.set rules' ~key:nt ~data:nt_prods', added' || added'')
         | None ->
             ( Map.set rules' ~key:nt
                 ~data:(Set.singleton (module Production) prod)
             , true ) )

let prod_lists_of_sets =
  Map.map ~f:(fun prods ->
      List.sort ~compare:(fun prod_1 prod_2 ->
          -Float.compare
             (Production.log_likelihood prod_1)
             (Production.log_likelihood prod_2) )
      @@ Set.to_list prods )

let rec rules_of_dsl ?(type_size_limit = 100) ?(rules = Map.empty (module Type))
    dsl req =
  let rules', added = expand_rules ~type_size_limit rules dsl req in
  if added then rules_of_dsl ~type_size_limit ~rules:rules' dsl req
  else prod_lists_of_sets rules'

let max_prob_parameterless rules =
  Map.fold rules
    ~init:(Map.empty (module Type))
    ~f:(fun ~key:nt ~data:prods max_prob' ->
      List.filter prods ~f:(fun prod ->
          List.is_empty @@ Production.nonterminals prod )
      |> List.sort ~compare:(fun pr_1 pr_2 ->
             -Float.compare pr_1.log_likelihood pr_2.log_likelihood )
      |> List.hd
      |> Option.value_map ~default:max_prob' ~f:(fun max_prod ->
             Map.add_exn max_prob' ~key:nt
               ~data:
                 (Derivation.Fields.create ~terminal:max_prod.terminal
                    ~nonterminals:[] ~nonterminal:nt
                    ~log_likelihood:max_prod.log_likelihood ) ) )

let rec max_prob_rest rules max_prob =
  let unevaluated = Set.diff (Map.key_set rules) (Map.key_set max_prob) in
  if not (Set.is_empty unevaluated) then
    max_prob_rest rules
    @@ Set.fold unevaluated ~init:max_prob ~f:(fun max_prob' nt ->
           Map.find_exn rules nt
           |> List.fold_until
                ~init:
                  (Derivation.Fields.create
                     ~terminal:(Primitive {name= "UNK"; ty= nt})
                     ~nonterminals:[] ~nonterminal:nt
                     ~log_likelihood:Float.neg_infinity )
                ~finish:Option.return
                ~f:(fun deriv prod ->
                  let nonterminals =
                    Production.nonterminals prod
                    |> List.filter_map ~f:(Map.find max_prob')
                  in
                  if List.length nonterminals = List.length prod.nonterminals
                  then
                    let deriv' =
                      Derivation.Fields.create ~terminal:prod.terminal
                        ~nonterminals ~nonterminal:nt
                        ~log_likelihood:
                          (List.fold nonterminals ~init:prod.log_likelihood
                             ~f:(fun ll_tot leaf ->
                               ll_tot +. leaf.log_likelihood ) )
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

let of_dsl ?(type_size_limit = 100) start dsl =
  let rules = rules_of_dsl ~type_size_limit dsl start in
  {start; rules; max_prob= max_prob_of_rules rules}
