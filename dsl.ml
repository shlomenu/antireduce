open Core
open Type
open Program
open Util.Yojson_util

type fast_unifier =
  type_context -> dc_type -> type_context * dc_type list * dc_type

type primitive_entry =
  {name: string; ty: dc_type; impl: program option; unifier: fast_unifier}

let yojson_of_primitive_entry ent =
  `Assoc
    [ ("name", yojson_of_string ent.name)
    ; ("ty", yojson_of_dc_type ent.ty)
    ; ("impl", yojson_of_option yojson_of_program ent.impl) ]

let primitive_entry_of_yojson = function
  | `Assoc [("name", j_name); ("ty", j_ty); ("impl", j_impl)] ->
      let ty = dc_type_of_yojson j_ty in
      { name= string_of_yojson j_name
      ; ty
      ; impl= option_of_yojson program_of_yojson j_impl
      ; unifier= make_fast_unifier ty }
  | _ ->
      failwith "primitive_entry_of_yojson: invalid JSON"

type dsl = {library: primitive_entry list; state_type: dc_type; size: int}
[@@deriving yojson]

let string_of_dsl dsl =
  Printf.sprintf "state type : %s\n" (string_of_dc_type dsl.state_type)
  ^ "\tt0\t$_\n"
  ^ String.concat ~sep:"\n"
      (List.map dsl.library ~f:(fun ent ->
           string_of_dc_type ent.ty ^ "\t" ^ ent.name ) )

let dsl_of_primitives state_type primitives =
  let library =
    List.map primitives ~f:(function
      | Primitive {name; ty} ->
          let unifier = make_fast_unifier ty in
          {name; ty; impl= None; unifier}
      | Invented (ty, b) ->
          let unifier = make_fast_unifier ty in
          {name= string_of_program b; ty; impl= Some b; unifier}
      | _ ->
          failwith "dsl_of_primitives: not a base primitive" )
  in
  let size = List.length library in
  {library; state_type; size}

exception DuplicatePrimitive

let dedup_dsl_of_primitives state_type primitives =
  let n_unique_prims =
    List.length @@ List.dedup_and_sort ~compare:compare_program primitives
  in
  if List.length primitives = n_unique_prims then
    { library=
        List.map primitives ~f:(function
          | Primitive {name; ty} ->
              {name; ty; impl= None; unifier= make_fast_unifier ty}
          | Invented (ty, b) ->
              { name= string_of_program b
              ; ty
              ; impl= Some b
              ; unifier= make_fast_unifier ty }
          | _ ->
              failwith
                "dedup_dsl_of_primitives: not a base or invented primitive" )
    ; state_type
    ; size= n_unique_prims }
  else raise DuplicatePrimitive

let primitive_of_entry ent =
  match ent.impl with
  | None ->
      Primitive {name= ent.name; ty= ent.ty}
  | Some b ->
      Invented (ent.ty, b)

let primitives_of_dsl dsl = List.map dsl.library ~f:primitive_of_entry

let prob_under_dsl ?(prob_of_index : float = 0.5) dsl p =
  if is_index p then prob_of_index
  else
    match
      List.find dsl.library ~f:(fun ent ->
          equal_program p (primitive_of_entry ent) )
    with
    | Some _ ->
        1. /. float_of_int dsl.size
    | None ->
        failwith ("prob_under_dsl: missing_primitive " ^ string_of_program p)

let log_prob_under_dsl dsl = Fn.compose log (prob_under_dsl dsl)

type unifying_expression =
  { expr: program
  ; parameters: dc_type list
  ; signature: dc_type
  ; context: type_context }

let unify_environment env req cxt =
  List.filter_mapi env ~f:(fun i ty ->
      let context, ty = apply_context cxt ty in
      let terminal_ty = terminal_of_type ty in
      if might_unify terminal_ty req then
        try
          let context = unify context terminal_ty req in
          let context, ty = apply_context context ty in
          let parameters = parameters_of_type ty in
          Some {expr= Index i; parameters; signature= ty; context}
        with UnificationFailure _ -> None
      else None )

let unifying_indices dsl env req cxt =
  let unified = unify_environment env req cxt in
  if equal_dc_type req dsl.state_type then
    let terminal_indices =
      List.filter_map unified ~f:(fun ent ->
          if List.is_empty ent.parameters then Some (int_of_index ent.expr)
          else None )
    in
    if List.is_empty terminal_indices then unified
    else
      let min_terminal_index = Util.fold1 ~f:min terminal_indices in
      List.filter unified ~f:(fun ent ->
          not
            ( is_index ent.expr
            && List.is_empty ent.parameters
            && int_of_index ent.expr <> min_terminal_index ) )
  else unified

let unifying_primitives dsl req cxt =
  List.filter_map dsl.library ~f:(fun ent ->
      try
        let terminal_ty = terminal_of_type ent.ty in
        if might_unify terminal_ty req then
          let context, parameters, signature = ent.unifier cxt req in
          Some {expr= primitive_of_entry ent; parameters; signature; context}
        else None
      with UnificationFailure _ -> None )

let unifying_expressions dsl env req cxt =
  unifying_indices dsl env req cxt @ unifying_primitives dsl req cxt

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

let likelihood_of_factorization dsl fact =
  let prob_of = prob_under_dsl dsl in
  fact.constant
  +. Hashtbl.fold fact.uses ~init:0. ~f:(fun ~key ~data log_prob ->
         log_prob +. (data *. log (prob_of key)) )
  -. Hashtbl.fold fact.normalizers ~init:0. ~f:(fun ~key ~data log_prob ->
         let probs = List.map key ~f:prob_of in
         let max_prob = List.reduce_exn ~f:Float.max probs in
         let lse =
           log @@ List.reduce_exn ~f:(fun s a -> s +. exp (a -. max_prob)) probs
         in
         log_prob +. (data *. lse) )

let factorize dsl req p =
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
        let exprs = unifying_expressions dsl env ty !cxt_ref in
        match walk_application_tree p' with
        | [] ->
            failwith "walk_application_tree"
        | f :: xs -> (
          match List.find exprs ~f:(fun {expr; _} -> equal_program expr f) with
          | None ->
              fact.constant <- Float.neg_infinity
          | Some expr ->
              cxt_ref := expr.context ;
              record_factor fact f @@ List.map exprs ~f:(fun {expr; _} -> expr) ;
              List.iter (List.zip_exn xs expr.parameters) ~f:(fun (x, x_ty) ->
                  go x_ty env x ) ) )
  in
  go req [] p ; fact

let likelihood_under_dsl dsl req p =
  likelihood_of_factorization dsl @@ factorize dsl req p
