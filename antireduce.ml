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

type compressed_generic_expr =
  | CGIndex of int
  | CGPrimitive of primitive
  | CGApply of compressed_generic_expr * compressed_generic_expr
  | CGAbstraction of dc_type * compressed_generic_expr
  | CGInvented of dc_type * dc_type * program
[@@deriving yojson, equal, compare, sexp_of, hash]

let rec program_of_compressed_generic_expr = function
  | CGIndex i ->
      Index i
  | CGPrimitive prim ->
      Primitive prim
  | CGApply (f, x) ->
      Apply
        ( program_of_compressed_generic_expr f
        , program_of_compressed_generic_expr x )
  | CGAbstraction (_, b) ->
      Abstraction (program_of_compressed_generic_expr b)
  | CGInvented (ununified_signature, _, b) ->
      Invented (ununified_signature, b)

let compressed_generic_of_unified_expression unified_signature = function
  | Index i ->
      CGIndex i
  | Primitive prim ->
      CGPrimitive prim
  | Invented (ununified_signature, b) ->
      CGInvented (ununified_signature, unified_signature, b)
  | _ ->
      failwith "primitive was not index or base primitive or invented primitive"

let rec enumerate_terminal ~max_size dsl env cxt req size =
  match req with
  | Arrow {left; right; _} ->
      enumerate_terminal ~max_size dsl (left :: env) cxt right size
      |> Option.value_map ~default:None ~f:(fun (b, cxt', size') ->
             Some (CGAbstraction (left, b), cxt', size') )
  | _ ->
      if size < max_size then
        let rec go remaining_unified =
          let i = Random.int @@ List.length remaining_unified in
          let selected = List.nth_exn remaining_unified i in
          let unselected =
            List.filteri remaining_unified ~f:(fun j _ -> j <> i)
          in
          match
            enumerate_parameters ~max_size dsl env selected.context
              selected.parameters
              (compressed_generic_of_unified_expression selected.signature
                 selected.expr )
              (size + 1)
          with
          | Some _ as r ->
              r
          | None ->
              if List.is_empty unselected then None else go unselected
        in
        go @@ unifying_expressions dsl env req cxt
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
                 (CGApply (f, x))
                 size' )

type annotated_expr =
  | AIndex of dc_type * int
  | APrimitive of dc_type * string
  | AApply of dc_type * dc_type * dc_type * annotated_expr * annotated_expr
  | AAbstraction of dc_type * annotated_expr

let string_of_annotated_program =
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

let rec annotated_of_program cxt env = function
  | Index i ->
      let ty = List.nth_exn env i in
      (cxt, ty, AIndex (ty, i))
  | Primitive {name; ty} ->
      let cxt, ty = instantiate_type cxt ty in
      (cxt, ty, APrimitive (ty, name))
  | Invented (_, b) ->
      annotated_of_program cxt env b
  | Abstraction b ->
      let parameter_type, cxt = make_type_id cxt in
      let cxt, terminal_type, b' =
        annotated_of_program cxt (parameter_type :: env) b
      in
      let signature = parameter_type @> terminal_type in
      (cxt, signature, AAbstraction (signature, b'))
  | Apply (f, x) ->
      let cxt, parameter_type, x' = annotated_of_program cxt env x in
      let cxt, terminal_type, f' = annotated_of_program cxt env f in
      let function_type =
        match f' with
        | AIndex (f_ty, _)
        | APrimitive (f_ty, _)
        | AAbstraction (f_ty, _)
        | AApply (f_ty, _, _, _, _) ->
            f_ty
      in
      ( cxt
      , terminal_type
      , AApply (terminal_type, function_type, parameter_type, f', x') )

let rec unify_annotations cxt req = function
  | AIndex (ty, i) ->
      let cxt = unify cxt req ty in
      let cxt, ty = apply_context cxt ty in
      (cxt, AIndex (ty, i))
  | APrimitive (ty, name) ->
      let cxt = unify cxt req ty in
      let cxt, ty = apply_context cxt ty in
      (cxt, APrimitive (ty, name))
  | AAbstraction (function_type, b) ->
      let cxt = unify cxt req function_type in
      let cxt, function_type = apply_context cxt function_type in
      let terminal_type =
        match function_type with
        | Arrow {right; _} ->
            right
        | _ ->
            failwith "AAbstraction: function type is not an arrow"
      in
      let cxt, b' = unify_annotations cxt terminal_type b in
      let cxt, function_type = apply_context cxt function_type in
      (cxt, AAbstraction (function_type, b'))
  | AApply (terminal_type, function_type, parameter_type, f, x) ->
      let cxt = unify cxt req terminal_type in
      let cxt = unify cxt (arrow parameter_type terminal_type) function_type in
      let cxt, terminal_type = apply_context cxt terminal_type in
      let cxt, function_type = apply_context cxt function_type in
      let cxt, parameter_type = apply_context cxt parameter_type in
      let cxt, x' = unify_annotations cxt parameter_type x in
      let cxt, f' = unify_annotations cxt function_type f in
      (cxt, AApply (terminal_type, function_type, parameter_type, f', x'))

type generic_expr =
  | GIndex of int
  | GPrimitive of string
  | GApply of generic_expr * generic_expr
  | GAbstraction of dc_type * generic_expr

let rec generic_of_annotated = function
  | AIndex (_, i) ->
      GIndex i
  | APrimitive (_, name) ->
      GPrimitive name
  | AApply (_, _, _, f, x) ->
      GApply (generic_of_annotated f, generic_of_annotated x)
  | AAbstraction (function_type, b) ->
      let parameter_type =
        match function_type with
        | Arrow {left; _} ->
            left
        | _ ->
            failwith "AAbstraction: function type is not an arrow"
      in
      GAbstraction (parameter_type, generic_of_annotated b)

let rec decompress_generic = function
  | CGIndex i ->
      GIndex i
  | CGPrimitive {name; _} ->
      GPrimitive name
  | CGApply (f, x) ->
      GApply (decompress_generic f, decompress_generic x)
  | CGAbstraction (parameter_type, b) ->
      GAbstraction (parameter_type, decompress_generic b)
  | CGInvented (_, unified_signature, b) ->
      generic_of_annotated
      @@ (fun (cxt, _, ap) -> snd @@ unify_annotations cxt unified_signature ap)
      @@ annotated_of_program empty_type_context [] b

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir ~size ~preprocess ~evaluate ~load_result ~nontrivial
    ~parse ~request ~yojson_of_output ~key_of_output ~yojson_of_key
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
           let program = parse @@ SU.to_string @@ SU.member "program" j in
           Hashtbl.update repr key ~f:(function
             | None ->
                 (None, Some program, SU.member "output" j)
             | Some _ ->
                 failwith "found multiple programs with the same output key" ) ;
           repr )
  in
  let end_time = Core_unix.time () +. exploration_timeout in
  while not Float.(Core_unix.time () > end_time) do
    let program_and_output =
      let open Option.Let_syntax in
      let%bind cg, _, _ =
        enumerate_terminal ~max_size:size dsl [] empty_type_context request 0
      in
      let cg, p = (preprocess cg, program_of_compressed_generic_expr cg) in
      let%bind _ =
        evaluate ~timeout:eval_timeout ~attempts p @@ decompress_generic cg
      in
      let o = load_result () in
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
             file_content ) )
  |> List.filter_map ~f:(fun (prev_path, cur_path, file_content') ->
         Caml.Sys.remove prev_path ;
         S.to_file cur_path file_content' ;
         if Filename.(prev_path <> cur_path) then
           Some (Filename.basename prev_path, Filename.basename cur_path)
         else None )
  |> List.unzip
