open Core

module ProgramList = struct
  module T = struct
    type t = Program.t list [@@deriving compare, sexp_of, hash]
  end

  include T
  include Comparator.Make (T)
end

type t =
  { normalizers: float Map.M(ProgramList).t
  ; uses: float Map.M(Program).t
  ; constant: float }

let show fact =
  String.concat ~sep:"\n"
    ( [Printf.sprintf "{likelihood_constant = %f;" fact.constant]
    @ ( Map.to_alist fact.uses
      |> List.map ~f:(fun (p, f) ->
             Printf.sprintf "uses[%s] = %f;" (Program.to_string p) f ) )
    @ ( Map.to_alist fact.normalizers
      |> List.map ~f:(fun (n, f) ->
             let n =
               List.map n ~f:Program.to_string |> String.concat ~sep:","
             in
             Printf.sprintf "normalizers[%s] = %f;" n f ) )
    @ ["}"] )

let empty =
  { normalizers= Map.empty (module ProgramList)
  ; uses= Map.empty (module Program)
  ; constant= 0.0 }

let mix =
  List.fold ~init:empty ~f:(fun mixed_fact (w, fact) ->
      { mixed_fact with
        uses=
          Map.merge mixed_fact.uses fact.uses ~f:(fun ~key:_ -> function
            | `Left data ->
                Some data
            | `Right data ->
                Some (w *. data)
            | `Both (k, data) ->
                Some (k +. (w *. data)) )
      ; normalizers=
          Map.merge mixed_fact.normalizers fact.normalizers ~f:(fun ~key:_ ->
            function
            | `Left data ->
                Some data
            | `Right data ->
                Some (w *. data)
            | `Both (k, data) ->
                Some (k +. (w *. data)) ) } )

let record fact used possible =
  let used_is_index = Program.is_index used in
  let used = if Program.is_index used then Program.Index 0 else used in
  { constant=
      ( fact.constant
      +.
      if used_is_index then
        -.( log @@ Float.of_int @@ List.length
          @@ List.filter possible ~f:Program.is_index )
      else 0.0 )
  ; uses=
      Map.update fact.uses used ~f:(function Some c -> c +. 1. | None -> 1.)
  ; normalizers=
      ( if List.exists possible ~f:Program.is_index then
        Program.Index 0
        :: List.filter possible ~f:(Fn.compose not Program.is_index)
      else possible )
      |> List.dedup_and_sort ~compare:Program.compare
      |> Map.update fact.normalizers ~f:(function
           | Some c ->
               c +. 1.
           | None ->
               1. ) }

let to_log_likelihood dsl fact =
  let ll_of = Dsl.log_likelihood_of_entry dsl in
  fact.constant
  +. Map.fold fact.uses ~init:0. ~f:(fun ~key ~data tot ->
         tot +. (data *. ll_of key) )
  -. Map.fold fact.normalizers ~init:0. ~f:(fun ~key ~data tot ->
         tot +. (data *. (Util.logsumexp @@ List.map key ~f:ll_of)) )

let factorize (dsl : Dsl.t) req p =
  let cxt, ty, ap =
    Typed_program.instantiate ~reduce_invented:false Type_context.empty [] p
  in
  let cxt = Typed_program.unify cxt req ap in
  let req' = snd @@ Type_context.apply cxt ty in
  assert (Type.equal req req') ;
  let rec go ?(fact = empty) ?(env = []) req' = function
    | Typed_program.TAbstraction (_, body) ->
        go ~fact
          ~env:(Type.left_of_arrow req' :: env)
          (Type.right_of_arrow req') body
    | p' -> (
      match Typed_program.list_of_applications req' p' with
      | (f_ty, f) :: xs ->
          let f' =
            match f with
            | TPrimitive (_, name) ->
                Dsl_entry.to_primitive
                @@ List.find_exn ~f:(fun ent ->
                       String.(Dsl_entry.stitch_name ent = name) )
                @@ Dsl.library dsl
            | TIndex (_, i) ->
                Index i
            | _ ->
                failwith
                  "factorize: root of application is not a base or invented \
                   primitive"
          in
          let fact' =
            record fact f'
              ( List.map ~f:Dsl_unification.expr
              @@ Dsl_unification.expressions dsl env f_ty Type_context.empty )
          in
          List.fold xs ~init:fact' ~f:(fun fact'' (x_ty, x) ->
              go ~fact:fact'' ~env x_ty x )
      | [] ->
          failwith
            "factorize: impossible: list_of_applications returned empty list" )
  in
  go req' @@ Typed_program.apply_context cxt ap

let inside_outside ?(epsilon = 0.001) dsl req frontier =
  let log_likelihoods, facts =
    List.map frontier ~f:(fun p ->
        let fact = factorize dsl req p in
        (to_log_likelihood dsl fact, fact) )
    |> List.unzip
  in
  let weighted_fact =
    let z = Util.logsumexp log_likelihoods in
    List.map log_likelihoods ~f:(fun ll -> exp (ll -. z))
    |> Fn.flip List.zip_exn facts |> mix
  in
  let possible_uses p =
    Map.fold ~init:0. weighted_fact.normalizers ~f:(fun ~key ~data c ->
        if List.mem ~equal:Program.equal key p then c +. data else c )
  in
  let uses p =
    Option.value_map ~default:0. ~f:Fn.id @@ Map.find weighted_fact.uses p
  in
  let dsl' =
    { dsl with
      var_log_likelihood=
        log (uses (Index 0) +. epsilon)
        -. log (possible_uses (Index 0) +. epsilon)
    ; library=
        List.map dsl.library ~f:(fun ent ->
            let prim = Dsl_entry.to_primitive ent in
            { ent with
              log_likelihood=
                log (uses prim +. epsilon) -. log (possible_uses prim +. epsilon)
            } ) }
  in
  (dsl', List.reduce_exn ~f:( +. ) @@ List.map facts ~f:(to_log_likelihood dsl'))

let log_likelihood_under_dsl dsl req p =
  to_log_likelihood dsl @@ factorize dsl req p
