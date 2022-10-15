open Core
open Type
open Program
open Util.Yojson_util

type fast_unifier = type_context -> dc_type -> type_context * dc_type list

type primitive_entry =
  { name: string
  ; ty: dc_type
  ; log_prob: float
  ; impl: program option
  ; unifier: fast_unifier }

let yojson_of_primitive_entry ent =
  `Assoc
    [ ("name", yojson_of_string ent.name)
    ; ("ty", yojson_of_dc_type ent.ty)
    ; ("log_prob", yojson_of_float ent.log_prob)
    ; ("impl", yojson_of_option yojson_of_program ent.impl) ]

let primitive_entry_of_yojson = function
  | `Assoc
      [ ("name", j_name)
      ; ("ty", j_ty)
      ; ("log_prob", j_log_prob)
      ; ("impl", j_impl) ] ->
      let name = string_of_yojson j_name in
      let ty = dc_type_of_yojson j_ty in
      let log_prob = float_of_yojson j_log_prob in
      let impl = option_of_yojson program_of_yojson j_impl in
      let unifier = make_fast_unifier ty in
      {name; ty; log_prob; impl; unifier}
  | _ ->
      failwith "primitive_entry_of_yojson: invalid JSON"

type grammar =
  { log_prob_any_type: float
  ; library: primitive_entry list
  ; state_type: dc_type option }
[@@deriving yojson]

let string_of_grammar gmr =
  ( match gmr.state_type with
  | Some state_ty ->
      Printf.sprintf "state type : %s\n" (string_of_dc_type state_ty)
  | None ->
      "" )
  ^ string_of_float gmr.log_prob_any_type
  ^ "\tt0\t$_\n"
  ^ String.concat ~sep:"\n"
      (List.map gmr.library ~f:(fun ent ->
           Float.to_string ent.log_prob
           ^ "\t" ^ string_of_dc_type ent.ty ^ "\t" ^ ent.name ) )

let grammar_of_primitives ?(state_type : dc_type option) primitives =
  let n_primitives = List.length primitives in
  let log_prob = -.log (float_of_int n_primitives) in
  let f = function
    | Primitive {name; ty} ->
        let unifier = make_fast_unifier ty in
        {name; ty; log_prob; impl= None; unifier}
    | Invented (ty, b) ->
        let unifier = make_fast_unifier ty in
        {name= string_of_program b; ty; log_prob; impl= Some b; unifier}
    | _ ->
        failwith "grammar_of_primitives: not a base primitive"
  in
  let library = List.map primitives ~f in
  {log_prob_any_type= log 0.5; library; state_type}

exception DuplicatePrimitive

let deduplicated_grammar_of_primitives ?(state_type = None) primitives =
  let n_unique_prims =
    List.length @@ List.dedup_and_sort ~compare:compare_program primitives
  in
  if List.length primitives = n_unique_prims then
    let log_prob = -.log (float_of_int n_unique_prims) in
    let f = function
      | Primitive {name; ty} ->
          {name; ty; log_prob; impl= None; unifier= make_fast_unifier ty}
      | Invented (ty, b) ->
          { name= string_of_program b
          ; ty
          ; log_prob
          ; impl= Some b
          ; unifier= make_fast_unifier ty }
      | _ ->
          failwith
            "deduplicated_grammar_of_primitives: not a base or invented \
             primitive"
    in
    let library = List.map primitives ~f in
    {log_prob_any_type= log 0.5; library; state_type}
  else raise DuplicatePrimitive

let primitive_of_entry ent =
  match ent.impl with
  | None ->
      Primitive {name= ent.name; ty= ent.ty}
  | Some b ->
      Invented (ent.ty, b)

let primitives_of_grammar gmr = List.map gmr.library ~f:primitive_of_entry

let log_prob_under_grammar gmr p =
  if is_index p then gmr.log_prob_any_type
  else
    let f ent =
      let p' = primitive_of_entry ent in
      if equal_program p' p then Some ent.log_prob else None
    in
    match List.filter_map gmr.library ~f with
    | [l] ->
        l
    | _ :: _ ->
        raise DuplicatePrimitive
    | [] ->
        let msg =
          "log_prob_under_grammar: missing primitive " ^ string_of_program p
        in
        failwith msg

type unifying_expression =
  { expr: program
  ; parameters: dc_type list
  ; context: type_context
  ; log_prob: float }

let unifying_expressions gmr env req cxt =
  let unifying_variables =
    let f i ty =
      let expr = Index i in
      let context, ty = apply_context cxt ty in
      let log_prob = gmr.log_prob_any_type in
      let terminal_ty = terminal_of_type ty in
      if might_unify terminal_ty req then
        try
          let context = unify context terminal_ty req in
          let context, ty = apply_context context ty in
          let parameters = parameters_of_type ty in
          Some {expr; parameters; context; log_prob}
        with UnificationFailure -> None
      else None
    in
    let unified = List.filter_mapi env ~f in
    let old_states_removed =
      match gmr.state_type with
      | Some state_ty when equal_dc_type state_ty req ->
          let terminal_indices =
            let f ent =
              if List.is_empty ent.parameters then Some (int_of_index ent.expr)
              else None
            in
            List.filter_map unified ~f
          in
          if List.is_empty terminal_indices then unified
          else
            let min_terminal_index = Util.fold1 min terminal_indices in
            let f ent =
              not
                ( is_index ent.expr
                && List.is_empty ent.parameters
                && int_of_index ent.expr <> min_terminal_index )
            in
            List.filter unified ~f
      | _ ->
          unified
    in
    let normalization_factor =
      log @@ Float.of_int @@ List.length old_states_removed
    in
    let f ent =
      let log_prob = ent.log_prob -. normalization_factor in
      {ent with log_prob}
    in
    List.map old_states_removed ~f
  in
  let unifying_programs =
    let f ent =
      try
        let terminal_ty = terminal_of_type ent.ty in
        if might_unify terminal_ty req then
          let context, parameters = ent.unifier cxt req in
          let expr = primitive_of_entry ent in
          let log_prob = ent.log_prob in
          Some {expr; parameters; context; log_prob}
        else None
      with UnificationFailure -> None
    in
    List.filter_map gmr.library ~f
  in
  let unified = unifying_variables @ unifying_programs in
  let normalization_factor =
    List.map unified ~f:(fun ent -> ent.log_prob) |> Util.lse_list
  in
  let f ent =
    let log_prob = ent.log_prob -. normalization_factor in
    {ent with log_prob}
  in
  List.map unified ~f

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
  let f (w, fact') =
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
              w *. data ) )
  in
  List.iter weighted_factorizations ~f ;
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
    if List.exists possible ~f:is_index then
      Index 0 :: List.filter possible ~f:(Fn.compose not is_index)
    else possible
  in
  let key = List.dedup_and_sort possible ~compare:compare_program in
  Hashtbl.update fact.normalizers key ~f:(function
    | Some f ->
        f +. 1.
    | None ->
        1. )

let likelihood_of_factorization gmr fact =
  let log_prob_of = log_prob_under_grammar gmr in
  fact.constant
  +. Hashtbl.fold fact.uses ~init:0. ~f:(fun ~key ~data log_prob ->
         let use_prob = log_prob_of key in
         log_prob +. (data *. use_prob) )
  -. Hashtbl.fold fact.normalizers ~init:0. ~f:(fun ~key ~data log_prob ->
         let normalizer_prob = Util.lse_list @@ List.map key ~f:log_prob_of in
         log_prob +. (data *. normalizer_prob) )

let factorize gmr req p =
  let rec walk_application_tree = function
    | Apply (f, x) ->
        walk_application_tree f @ [x]
    | tree ->
        [tree]
  in
  let fact = empty_factorization () in
  let cxt_ref = ref empty_type_context in
  let rec go ty env p' =
    match ty with
    | Arrow {left; right; _} ->
        let env = left :: env in
        let p' = strip_n_abstractions 1 p' in
        go right env p'
    | _ -> (
        let exprs = unifying_expressions gmr env ty !cxt_ref in
        match walk_application_tree p' with
        | [] ->
            failwith "walk_application_tree"
        | f :: xs -> (
            let used =
              let f {expr; _} = equal_program expr f in
              List.find exprs ~f
            in
            match used with
            | None ->
                fact.constant <- Float.neg_infinity
            | Some expr ->
                cxt_ref := expr.context ;
                record_factor fact f
                @@ List.map exprs ~f:(fun {expr; _} -> expr) ;
                List.iter (List.zip_exn xs expr.parameters) ~f:(fun (x, x_ty) ->
                    go x_ty env x ) ) )
  in
  go req [] p ; fact

let likelihood_under_grammar gmr req p =
  likelihood_of_factorization gmr @@ factorize gmr req p
