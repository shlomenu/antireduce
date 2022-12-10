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

type partial_program =
  | PIndex of int
  | PAbstraction of partial_program
  | PApply of partial_program * partial_program
  | PPrimitive of primitive
  | PInvented of dc_type * program
  | Hole of dc_type

let rec partial_of_program = function
  | Index i ->
      PIndex i
  | Abstraction b ->
      PAbstraction (partial_of_program b)
  | Apply (f, x) ->
      PApply (partial_of_program f, partial_of_program x)
  | Primitive prim ->
      PPrimitive prim
  | Invented (ty, b) ->
      PInvented (ty, b)

let rec program_of_partial = function
  | PIndex i ->
      Index i
  | PAbstraction b ->
      Abstraction (program_of_partial b)
  | PApply (f, x) ->
      Apply (program_of_partial f, program_of_partial x)
  | PPrimitive prim ->
      Primitive prim
  | PInvented (ty, b) ->
      Invented (ty, b)
  | Hole _ ->
      failwith "cannot convert partial program with holes to program"

let string_of_partial_program (p : partial_program) : string =
  let rec go parenthesized : partial_program -> string = function
    | PIndex j ->
        "$" ^ string_of_int j
    | PAbstraction b ->
        "(lambda " ^ go true b ^ ")"
    | PApply (f, x) ->
        let body = go false f ^ " " ^ go true x in
        if parenthesized then "(" ^ body ^ ")" else body
    | PPrimitive {name; _} ->
        name
    | PInvented (_, b) ->
        "#" ^ string_of_program b
    | Hole ty ->
        Printf.sprintf "<%s>" (string_of_dc_type ty)
  in
  go true p

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
             Some (PAbstraction b, cxt', size') )
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
              (partial_of_program selected.expr)
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
                 (PApply (f, x))
                 size' )

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir ~size ~evaluate ~nontrivial ~saveable_output ~parse
    ~request ~yojson_of_output ~output_of_yojson ~key_of_output ~yojson_of_key
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
           let output = output_of_yojson @@ SU.member "output" j in
           Hashtbl.update repr key ~f:(function
             | None ->
                 (None, Some (program, output))
             | Some _ ->
                 failwith "found multiple programs with the same output key" ) ;
           repr )
  in
  let end_time = Core_unix.time () +. exploration_timeout in
  while not Float.(Core_unix.time () > end_time) do
    let program_and_output =
      let open Option.Let_syntax in
      let%bind p, _, _ =
        enumerate_terminal ~max_size:size dsl [] empty_type_context request 0
      in
      let p = program_of_partial p in
      let%bind o = evaluate ~timeout:eval_timeout ~attempts p in
      if nontrivial o then Option.return (p, o) else None
    in
    Option.value_map program_and_output ~default:() ~f:(fun (p, o) ->
        Hashtbl.update representations (key_of_output o) ~f:(function
          | None ->
              (Some (p, saveable_output o), None)
          | Some (None, None) ->
              failwith "unpopulated entry"
          | Some (None, (Some (prev_p, _) as prev_best)) ->
              let cur_best =
                if size_of_program p < size_of_program prev_p then
                  Some (p, saveable_output o)
                else None
              in
              (cur_best, prev_best)
          | Some ((Some (cur_p, _) as cur_best), prev_best) ->
              let cur_best =
                if size_of_program p < size_of_program cur_p then
                  Some (p, saveable_output o)
                else cur_best
              in
              (cur_best, prev_best) ) )
  done ;
  let n_new, n_replaced, prev_files, cur_files =
    Hashtbl.fold representations ~init:(0, 0, [], [])
      ~f:(fun ~key ~data (n_new, n_replaced, prev_files, cur_files) ->
        match data with
        | None, None ->
            failwith "unpopulated entry"
        | None, Some _ ->
            (n_new, n_replaced, prev_files, cur_files)
        | Some (cur_p, cur_o), prev_best ->
            let path_of s =
              Filename.concat representations_dir
              @@ Fn.flip ( ^ ) ".json" @@ Md5.to_hex @@ Md5.digest_string s
            in
            let cur_ps = string_of_program cur_p in
            let cur_path = path_of cur_ps in
            let n_new', n_replaced', prev_files', cur_files' =
              match prev_best with
              | Some (prev_p, _) ->
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
                 ; ("output", yojson_of_output cur_o)
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
