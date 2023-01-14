open Core
open Type
open Program
open Util.Yojson_util

type fast_unifier = type_context -> dc_type -> type_context * dc_type list

type primitive_entry =
  { dc_name: string
  ; stitch_name: string
  ; ty: dc_type
  ; impl: program option
  ; log_likelihood: float
  ; unifier: fast_unifier }

let yojson_of_primitive_entry ent =
  `Assoc
    [ ("dc_name", yojson_of_string ent.dc_name)
    ; ("stitch_name", yojson_of_string ent.stitch_name)
    ; ("ty", yojson_of_dc_type ent.ty)
    ; ("impl", yojson_of_option yojson_of_program ent.impl)
    ; ("log_likelihood", yojson_of_float ent.log_likelihood) ]

let primitive_entry_of_yojson = function
  | `Assoc
      [ ("dc_name", j_dc_name)
      ; ("stitch_name", j_stitch_name)
      ; ("ty", j_ty)
      ; ("impl", j_impl)
      ; ("log_likelihood", j_ll) ] ->
      let ty = dc_type_of_yojson j_ty in
      { dc_name= string_of_yojson j_dc_name
      ; stitch_name= string_of_yojson j_stitch_name
      ; ty
      ; impl= option_of_yojson program_of_yojson j_impl
      ; unifier= make_fast_unifier ty
      ; log_likelihood= float_of_yojson j_ll }
  | _ ->
      failwith "primitive_entry_of_yojson: invalid json"

type dsl =
  { library: primitive_entry list
  ; state_type: dc_type
  ; var_log_likelihood: float
  ; size: int
  ; mass: int }
[@@deriving yojson]

let string_of_dsl dsl =
  Printf.sprintf "state type : %s\n" (string_of_dc_type dsl.state_type)
  ^ "\tt0\t$_\n"
  ^ String.concat ~sep:"\n"
      (List.map dsl.library ~f:(fun ent ->
           string_of_dc_type ent.ty ^ "\t" ^ ent.dc_name ) )

let dsl_of_primitives state_type primitives =
  let size = List.length primitives in
  let n_primitives = float_of_int size in
  { library=
      List.map primitives ~f:(function
        | Primitive {name; ty} ->
            { dc_name= name
            ; stitch_name= name
            ; ty
            ; impl= None
            ; unifier= make_fast_unifier ty
            ; log_likelihood= log (1. /. n_primitives) }
        | Invented {name; ty; body} ->
            { dc_name= string_of_program body
            ; stitch_name= name
            ; ty
            ; impl= Some body
            ; unifier= make_fast_unifier ty
            ; log_likelihood= log (1. /. n_primitives) }
        | _ ->
            failwith "dsl_of_primitives: not a base primitive" )
  ; state_type
  ; var_log_likelihood= log 0.5
  ; size
  ; mass= List.reduce_exn ~f:( + ) @@ List.map primitives ~f:mass_of_program }

exception DuplicatePrimitive

let dedup_dsl_of_primitives state_type primitives =
  let size =
    List.length @@ List.dedup_and_sort ~compare:compare_program primitives
  in
  let n_primitives = float_of_int size in
  if List.length primitives = size then
    { library=
        List.map primitives ~f:(function
          | Primitive {name; ty} ->
              { dc_name= name
              ; stitch_name= name
              ; ty
              ; impl= None
              ; unifier= make_fast_unifier ty
              ; log_likelihood= log (1. /. n_primitives) }
          | Invented {name; ty; body} ->
              { dc_name= string_of_program body
              ; stitch_name= name
              ; ty
              ; impl= Some body
              ; unifier= make_fast_unifier ty
              ; log_likelihood= log (1. /. n_primitives) }
          | _ ->
              failwith
                "dedup_dsl_of_primitives: not a base or invented primitive" )
    ; state_type
    ; var_log_likelihood= log 0.5
    ; size
    ; mass= List.reduce_exn ~f:( + ) @@ List.map primitives ~f:mass_of_program
    }
  else raise DuplicatePrimitive

let primitive_of_entry ent =
  match ent.impl with
  | None ->
      Primitive {name= ent.dc_name; ty= ent.ty}
  | Some body ->
      Invented {name= ent.stitch_name; ty= ent.ty; body}

let primitives_of_dsl dsl = List.map dsl.library ~f:primitive_of_entry

let log_likelihood_under_dsl dsl p =
  if is_index p then dsl.var_log_likelihood
  else
    match
      List.filter_map dsl.library ~f:(fun ent ->
          if equal_program p (primitive_of_entry ent) then Some ent else None )
    with
    | [ent] ->
        ent.log_likelihood
    | _ :: _ ->
        failwith
          ( Format.sprintf "log_likelihood_under_dsl: duplicate_primitive %s"
          @@ string_of_program p )
    | [] ->
        failwith
          ( Format.sprintf "log_likelihood_under_dsl: missing_primitive %s"
          @@ string_of_program p )

type unifying_expression =
  { expr: program
  ; parameters: dc_type list
  ; context: type_context
  ; log_likelihood: float }

let unify_environment dsl env req cxt =
  List.filter_mapi env ~f:(fun i ty ->
      let context, ty = apply_context cxt ty in
      let l_ty, l_req = (list_of_arrows ty, list_of_arrows req) in
      let size_ty, size_req = (List.length l_ty, List.length l_req) in
      if size_req > size_ty then None
      else
        let terminal_ty =
          arrows_of_list @@ List.drop l_ty (size_ty - size_req)
        in
        if might_unify terminal_ty req then
          try
            let context = unify context terminal_ty req in
            let context, ty = apply_context context ty in
            let parameters =
              List.take (list_of_arrows ty) (size_ty - size_req)
            in
            Some
              { expr= Index i
              ; parameters
              ; context
              ; log_likelihood= dsl.var_log_likelihood }
          with UnificationFailure _ -> None
        else None )

let unifying_indices dsl env req cxt =
  let unified = unify_environment dsl env req cxt in
  let permitted_unified =
    if equal_dc_type req dsl.state_type then
      let terminal_indices =
        List.filter_map unified ~f:(fun ent ->
            if List.is_empty ent.parameters then Some (int_of_index ent.expr)
            else None )
      in
      if List.is_empty terminal_indices then unified
      else
        let min_terminal_index = List.reduce_exn ~f:min terminal_indices in
        List.filter unified ~f:(fun ent ->
            not
              ( is_index ent.expr
              && List.is_empty ent.parameters
              && int_of_index ent.expr <> min_terminal_index ) )
    else unified
  in
  let tot = log @@ Float.of_int @@ List.length permitted_unified in
  List.map permitted_unified ~f:(fun ent ->
      {ent with log_likelihood= ent.log_likelihood -. tot} )

let unifying_primitives dsl req cxt =
  List.filter_map dsl.library ~f:(fun ent ->
      try
        let context, parameters = ent.unifier cxt req in
        Some
          { expr= primitive_of_entry ent
          ; parameters
          ; context
          ; log_likelihood= ent.log_likelihood }
      with UnificationFailure _ -> None )

let unifying_expressions dsl env req cxt =
  let unified =
    unifying_indices dsl env req cxt @ unifying_primitives dsl req cxt
  in
  if List.is_empty unified then unified
  else
    let z =
      Util.logsumexp @@ List.map unified ~f:(fun ent -> ent.log_likelihood)
    in
    List.map unified ~f:(fun ent ->
        {ent with log_likelihood= ent.log_likelihood -. z} )

type 'a likelihood_factorization =
  { normalizers: ('a list, float) Hashtbl.t
  ; uses: ('a, float) Hashtbl.t
  ; mutable constant: float }

module ProgramList = struct
  type t = program list [@@deriving compare, sexp_of, hash]
end

module StringList = struct
  type t = string list [@@deriving compare, sexp_of, hash]
end

let yojson_of_likelihood_factorization f fact =
  `Assoc
    [ ( "normalizers"
      , yojson_of_hashtbl (yojson_of_list f) yojson_of_float fact.normalizers )
    ; ("uses", yojson_of_hashtbl f yojson_of_float fact.uses)
    ; ("constant", yojson_of_float fact.constant) ]

let likelihood_factorization_of_yojson f = function
  | `Assoc
      [ ("normalizers", j_normalizers)
      ; ("uses", j_uses)
      ; ("constant", j_constant) ] ->
      { normalizers=
          hashtbl_of_yojson
            (module StringList)
            (list_of_yojson f) float_of_yojson j_normalizers
      ; uses= hashtbl_of_yojson (module String) f float_of_yojson j_uses
      ; constant= float_of_yojson j_constant }
  | _ ->
      failwith "corrupted json"

let stringify_factorization fact =
  { fact with
    normalizers=
      (let init = Hashtbl.create (module StringList) in
       Hashtbl.fold fact.normalizers ~init ~f:(fun ~key ~data new_tbl ->
           Hashtbl.set new_tbl ~key:(List.map key ~f:string_of_program) ~data ;
           new_tbl ) )
  ; uses=
      (let init = Hashtbl.create (module String) in
       Hashtbl.fold fact.uses ~init ~f:(fun ~key ~data new_tbl ->
           Hashtbl.set new_tbl ~key:(string_of_program key) ~data ;
           new_tbl ) ) }

let show_factorization fact =
  String.concat ~sep:"\n"
    ( [Printf.sprintf "{likelihood_constant = %f;" fact.constant]
    @ ( Hashtbl.to_alist fact.uses
      |> List.map ~f:(fun (p, f) ->
             Printf.sprintf "uses[%s] = %f;" (string_of_program p) f ) )
    @ ( Hashtbl.to_alist fact.normalizers
      |> List.map ~f:(fun (n, f) ->
             let n =
               List.map n ~f:string_of_program |> String.concat ~sep:","
             in
             Printf.sprintf "normalizers[%s] = %f;" n f ) )
    @ ["}"] )

let empty_factorization () =
  { normalizers= Hashtbl.create (module ProgramList)
  ; uses= Hashtbl.create (module Program)
  ; constant= 0.0 }

let mix_factorizations weighted_factorizations =
  let mixed = empty_factorization () in
  List.iter weighted_factorizations ~f:(fun (w, fact') ->
      Hashtbl.iteri fact'.uses ~f:(fun ~key ~data ->
          Hashtbl.update mixed.uses key ~f:(function
            | Some k ->
                k +. (w *. data)
            | None ->
                w *. data ) ) ;
      Hashtbl.iteri fact'.normalizers ~f:(fun ~key ~data ->
          Hashtbl.update mixed.normalizers key ~f:(function
            | Some k ->
                k +. (w *. data)
            | None ->
                w *. data ) ) ) ;
  mixed

let record_factor fact used possible =
  let constant =
    if is_index used then
      -.(log @@ Float.of_int @@ List.length @@ List.filter possible ~f:is_index)
    else 0.0
  in
  fact.constant <- fact.constant +. constant ;
  let used = if is_index used then Index 0 else used in
  Hashtbl.update fact.uses used ~f:(function Some f -> f +. 1. | None -> 1.) ;
  let possible =
    ( if List.exists possible ~f:is_index then
      Index 0 :: List.filter possible ~f:(Fn.compose not is_index)
    else possible )
    |> List.dedup_and_sort ~compare:compare_program
  in
  Hashtbl.update fact.normalizers possible ~f:(function
    | Some f ->
        f +. 1.
    | None ->
        1. )

let log_likelihood_of_factorization dsl fact =
  let ll_of = log_likelihood_under_dsl dsl in
  fact.constant
  +. Hashtbl.fold fact.uses ~init:0. ~f:(fun ~key ~data tot ->
         tot +. (data *. ll_of key) )
  -. Hashtbl.fold fact.normalizers ~init:0. ~f:(fun ~key ~data tot ->
         tot +. (data *. (Util.logsumexp @@ List.map key ~f:ll_of)) )

let factorize dsl req p =
  let rec walk_application_tree = function
    | Apply (f, x) ->
        walk_application_tree f @ [x]
    | tree ->
        [tree]
  in
  let fact = empty_factorization () in
  let cxt_ref = ref empty_type_context in
  let rec go env p' ty =
    match ty with
    | Arrow {left; right; _} ->
        go (left :: env) (strip_n_abstractions 1 p') right
    | _ -> (
      match walk_application_tree p' with
      | [] ->
          failwith "walk_application_tree"
      | f :: xs -> (
          let unified = unifying_expressions dsl env ty !cxt_ref in
          match
            List.find unified ~f:(fun {expr; _} -> equal_program expr f)
          with
          | None ->
              failwith
                "primitive type did not unify during likelihood factorization"
          | Some expr ->
              cxt_ref := expr.context ;
              record_factor fact f
              @@ List.map unified ~f:(fun {expr; _} -> expr) ;
              List.iter2_exn xs expr.parameters ~f:(go env) ) )
  in
  go [] p req ; fact

let log_likelihood_under_dsl dsl req p =
  log_likelihood_of_factorization dsl @@ factorize dsl req p

let inside_outside ?(epsilon = 0.001) dsl req frontier =
  let log_likelihoods, facts =
    List.map frontier ~f:(fun p ->
        let fact = factorize dsl req p in
        (log_likelihood_of_factorization dsl fact, fact) )
    |> List.unzip
  in
  let weighted_fact =
    let z = Util.logsumexp log_likelihoods in
    List.map log_likelihoods ~f:(fun ll -> exp (ll -. z))
    |> Fn.flip List.zip_exn facts |> mix_factorizations
  in
  let possible_uses p =
    Hashtbl.fold ~init:0. weighted_fact.normalizers ~f:(fun ~key ~data c ->
        if List.mem ~equal:equal_program key p then c +. data else c )
  in
  let uses p =
    Option.value_map ~default:0. ~f:Fn.id @@ Hashtbl.find weighted_fact.uses p
  in
  let dsl' =
    { dsl with
      var_log_likelihood=
        log (uses (Index 0) +. epsilon)
        -. log (possible_uses (Index 0) +. epsilon)
    ; library=
        List.map dsl.library ~f:(fun ent ->
            let prim = primitive_of_entry ent in
            { ent with
              log_likelihood=
                log (uses prim +. epsilon) -. log (possible_uses prim +. epsilon)
            } ) }
  in
  ( dsl'
  , List.reduce_exn ~f:( +. )
    @@ List.map facts ~f:(log_likelihood_of_factorization dsl') )
