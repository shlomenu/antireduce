module Type = Type
module Program = Program
module Dsl = Dsl
module Parser = Parser
module Versions = Versions
module Compression = Compression
module Util = Util
module S = Yojson.Safe
module SU = Yojson.Safe.Util
open Core
open Type
open Program
open Dsl

let rec parameters_length_aux dsl len = function
  | [] ->
      len
  | last :: [] when equal_dc_type last dsl.state_type ->
      len
  | _ :: rest ->
      parameters_length_aux dsl (len + 1) rest

let parameters_length dsl = parameters_length_aux dsl 0

let rec enumerate_terminal ~max_size dsl env cxt req size =
  match req with
  | Arrow {left; right; _} ->
      enumerate_terminal ~max_size dsl (left :: env) cxt right size
      |> Option.value_map ~default:None ~f:(fun (b, cxt', size') ->
             Some (Abstraction b, cxt', size') )
  | _ ->
      if size < max_size then
        let unified = unifying_expressions dsl env req cxt in
        let i = Random.int @@ List.length unified in
        let selected = List.nth_exn unified i in
        enumerate_parameters ~max_size dsl env selected.context
          selected.parameters selected.expr (size + 1)
      else None

and enumerate_parameters ~max_size dsl env cxt parameters f size =
  match parameters with
  | [] ->
      Some (f, cxt, size)
  | x_ty :: rest ->
      if parameters_length dsl parameters > max_size - size then None
      else
        let cxt, x_ty = apply_context cxt x_ty in
        enumerate_terminal ~max_size dsl env cxt x_ty size
        |> Option.value_map ~default:None ~f:(fun (x, cxt', size') ->
               enumerate_parameters ~max_size dsl env cxt' rest
                 (Apply (f, x))
                 size' )

type annotated_expr =
  | AIndex of dc_type * int
  | APrimitive of dc_type * string
  | AApply of dc_type * dc_type * dc_type * annotated_expr * annotated_expr
  | AAbstraction of dc_type * annotated_expr

let string_of_annotated_expr =
  let rec go parenthesized cxt = function
    | AIndex (ty, j) ->
        let _, ty = apply_context cxt ty in
        "($" ^ string_of_int j ^ " : " ^ string_of_dc_type ty ^ ")"
    | AAbstraction (ty, b) ->
        let cxt, ty = apply_context cxt ty in
        "((lambda " ^ go true cxt b ^ ") : " ^ string_of_dc_type ty ^ ")"
    | AApply (_, _, _, f, x) ->
        let body = go false cxt f ^ " " ^ go true cxt x in
        if parenthesized then "(" ^ body ^ ")" else body
    | APrimitive (ty, name) ->
        let _, ty = apply_context cxt ty in
        "(" ^ name ^ " : " ^ string_of_dc_type ty ^ ")"
  in
  go true

let rec instantiate_all cxt env = function
  | Index i ->
      let ty = List.nth_exn env i in
      (cxt, ty, AIndex (ty, i))
  | Primitive {name; ty} ->
      let cxt, ty = instantiate_type cxt ty in
      (cxt, ty, APrimitive (ty, name))
  | Invented (_, b) ->
      instantiate_all cxt [] b
  | Abstraction b ->
      let parameter_type, cxt = make_type_id cxt in
      let cxt, terminal_type, b' =
        instantiate_all cxt (parameter_type :: env) b
      in
      let function_type = parameter_type @> terminal_type in
      (cxt, function_type, AAbstraction (function_type, b'))
  | Apply (f, x) ->
      let cxt, function_type, f' = instantiate_all cxt env f in
      let cxt, parameter_type, x' = instantiate_all cxt env x in
      let cxt, terminal_type =
        match function_type with
        | Arrow {right; _} ->
            (cxt, right)
        | Constructor _ ->
            failwith
            @@ Format.sprintf "function_type is not an arrow: %s"
            @@ string_of_annotated_expr cxt f'
        | Id _ ->
            let terminal_type, cxt = make_type_id cxt in
            (cxt, terminal_type)
      in
      let cxt = unify cxt function_type (parameter_type @> terminal_type) in
      ( cxt
      , terminal_type
      , AApply (terminal_type, function_type, parameter_type, f', x') )

let rec unify_all cxt req = function
  | AIndex (ty, _) | APrimitive (ty, _) ->
      unify cxt req ty
  | AAbstraction (function_type, b) ->
      let cxt = unify cxt req function_type in
      unify_all cxt (right_of_arrow req) b
  | AApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt = unify cxt req terminal_type in
      let cxt = unify_all cxt function_type f in
      unify_all cxt parameter_type x

let rec apply_context_all cxt = function
  | AIndex (ty, i) ->
      let _, ty' = apply_context cxt ty in
      AIndex (ty', i)
  | APrimitive (ty, name) ->
      let _, ty' = apply_context cxt ty in
      APrimitive (ty', name)
  | AAbstraction (function_type, b) ->
      let cxt, function_type' = apply_context cxt function_type in
      AAbstraction (function_type', apply_context_all cxt b)
  | AApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt, terminal_type' = apply_context cxt terminal_type in
      let cxt, function_type' = apply_context cxt function_type in
      let cxt, parameter_type' = apply_context cxt parameter_type in
      let f' = apply_context_all cxt f in
      let x' = apply_context_all cxt x in
      AApply (terminal_type', function_type', parameter_type', f', x')

type generic_expr =
  | GIndex of int
  | GPrimitive of string
  | GApply of generic_expr * generic_expr
  | GAbstraction of dc_type * generic_expr

let string_of_generic_expr =
  let rec go parenthesized cxt = function
    | GIndex j ->
        "$" ^ string_of_int j
    | GAbstraction (ty, b) ->
        let cxt, ty = apply_context cxt ty in
        "(lambda (" ^ string_of_dc_type ty ^ ") " ^ go true cxt b ^ ")"
    | GApply (f, x) ->
        let body = go false cxt f ^ " " ^ go true cxt x in
        if parenthesized then "(" ^ body ^ ")" else body
    | GPrimitive name ->
        name
  in
  go true

let rec generic_of_annotated = function
  | AIndex (_, i) ->
      GIndex i
  | APrimitive (_, name) ->
      GPrimitive name
  | AApply (_, _, _, f, x) ->
      GApply (generic_of_annotated f, generic_of_annotated x)
  | AAbstraction (function_type, b) ->
      GAbstraction (left_of_arrow function_type, generic_of_annotated b)

let generic_expr_of_program req p =
  let cxt, _, ap =
    instantiate_all empty_type_context []
    @@ beta_normal_form ~reduce_invented:true p
  in
  let cxt = unify_all cxt req ap in
  generic_of_annotated @@ apply_context_all cxt ap

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir ~size ~apply_to_state ~evaluate ~retrieve_result
    ~nontrivial ~parse ~request ~yojson_of_output ~key_of_output ~yojson_of_key
    ~key_of_yojson key_module =
  if not (equal_dc_type request @@ arrow dsl.state_type dsl.state_type) then
    failwith
      "explore: requested type must be of the form: dsl.state_type -> \
       dsl.state_type" ;
  let representations =
    Caml.Sys.readdir representations_dir
    |> Array.fold ~init:(Hashtbl.create key_module) ~f:(fun repr filename ->
           let j =
             S.from_file @@ Filename.concat representations_dir filename
           in
           let key = key_of_yojson @@ SU.member "key" j in
           let p = parse @@ SU.to_string @@ SU.member "program" j in
           Hashtbl.update repr key ~f:(function
             | None ->
                 (None, Some p, SU.member "output" j)
             | Some _ ->
                 failwith "found multiple programs with the same output key" ) ;
           repr )
  in
  let end_time = Core_unix.time () +. exploration_timeout in
  while not Float.(Core_unix.time () > end_time) do
    let program_and_output =
      let open Option.Let_syntax in
      Random.self_init () ;
      let%bind p, _, _ =
        enumerate_terminal ~max_size:size dsl [] empty_type_context request 0
      in
      let p_applied = apply_to_state p in
      let%bind _ =
        evaluate ~timeout:eval_timeout ~attempts p_applied
        @@ generic_expr_of_program dsl.state_type p_applied
      in
      let o = retrieve_result () in
      if nontrivial o then Option.return (p, o) else None
    in
    Option.value_map program_and_output ~default:() ~f:(fun (p, o) ->
        Hashtbl.update representations (key_of_output o) ~f:(function
          | None ->
              (Some p, None, yojson_of_output o)
          | Some (None, None, _) ->
              failwith "unpopulated entry"
          | Some (None, (Some prev_p as prev_best), o) ->
              let cur_best =
                if size_of_program p < size_of_program prev_p then Some p
                else None
              in
              (cur_best, prev_best, o)
          | Some ((Some cur_p as cur_best), prev_best, o) ->
              let cur_best =
                if size_of_program p < size_of_program cur_p then Some p
                else cur_best
              in
              (cur_best, prev_best, o) ) )
  done ;
  let n_new, n_replaced, prev_files, cur_files =
    Hashtbl.fold representations ~init:(0, 0, [], [])
      ~f:(fun ~key ~data (n_new, n_replaced, prev_files, cur_files) ->
        match data with
        | None, None, _ ->
            failwith "unpopulated entry"
        | None, Some _, _ ->
            (n_new, n_replaced, prev_files, cur_files)
        | Some cur_p, prev_best, o_save ->
            let path_of s =
              Filename.concat representations_dir
              @@ Fn.flip ( ^ ) ".json" @@ Md5.to_hex @@ Md5.digest_string s
            in
            let cur_ps = string_of_program cur_p in
            let cur_path = path_of cur_ps in
            let n_new', n_replaced', prev_files', cur_files' =
              match prev_best with
              | Some prev_p ->
                  let prev_path = path_of @@ string_of_program prev_p in
                  Caml.Sys.remove prev_path ;
                  ( n_new
                  , n_replaced + 1
                  , Filename.basename prev_path :: prev_files
                  , Filename.basename cur_path :: cur_files )
              | None ->
                  (n_new + 1, n_replaced, prev_files, cur_files)
            in
            S.to_file cur_path
            @@ `Assoc
                 [ ("program", `String cur_ps)
                 ; ("size", `Int (size_of_program cur_p))
                 ; ( "mass"
                   , `Int
                       ( mass_of_program
                       @@ beta_normal_form ~reduce_invented:true cur_p ) )
                 ; ("output", o_save)
                 ; ("key", yojson_of_key key) ] ;
            (n_new', n_replaced', prev_files', cur_files') )
  in
  S.to_channel Out_channel.stdout
    (`Assoc
      [ ("new", `Int n_new)
      ; ("replaced", `Int n_replaced)
      ; ("prev_files", yojson_of_list yojson_of_string prev_files)
      ; ("cur_files", yojson_of_list yojson_of_string cur_files) ] )

let load_representations_from parse representations_dir frontier =
  Array.filter_map frontier ~f:(fun filename ->
      let path = Filename.concat representations_dir filename in
      let j = S.from_file path in
      Some (parse @@ SU.to_string @@ SU.member "program" j, path, j) )
  |> Array.to_list |> Util.unzip3

let overwrite_representations programs' paths file_contents =
  List.zip_exn programs' file_contents
  |> List.zip_exn paths
  |> List.fold_right
       ~init:(Set.empty (module String), [])
       ~f:(fun (path, (program', file_content)) (s, l) ->
         if not (Set.mem s path) then
           (Set.add s path, (path, program', file_content) :: l)
         else (s, l) )
  |> snd
  |> List.map ~f:(fun (path, program', file_content) ->
         ( path
         , Filename.concat (Filename.dirname path)
           @@ Fn.flip ( ^ ) ".json" @@ Md5.to_hex @@ Md5.digest_string
           @@ string_of_program program'
         , Util.Yojson_util.sub "program"
             (`String (string_of_program program'))
             file_content
           |> Util.Yojson_util.sub "size" (`Int (size_of_program program'))
           |> Util.Yojson_util.sub "mass"
                (`Int
                  ( mass_of_program
                  @@ beta_normal_form ~reduce_invented:true program' ) ) ) )
  |> List.filter_map ~f:(fun (prev_path, cur_path, file_content') ->
         Caml.Sys.remove prev_path ;
         S.to_file cur_path file_content' ;
         if Filename.(prev_path <> cur_path) then
           Some (Filename.basename prev_path, Filename.basename cur_path)
         else None )
  |> List.unzip
