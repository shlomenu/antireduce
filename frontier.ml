open Core
open Program
module S = Yojson.Safe
module SU = Yojson.Safe.Util

let load_representations_from parse representations_dir frontier =
  List.map frontier ~f:(fun filename ->
      let path = Filename.concat representations_dir filename in
      let j = S.from_file path in
      (parse @@ SU.to_string @@ SU.member "program" j, path, j) )
  |> List.unzip3

let repr_path dir p =
  Filename.concat dir @@ Fn.flip ( ^ ) ".json" @@ Md5.to_hex
  @@ Md5.digest_string
  @@ string_of_program ~format:`Dreamcoder p

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
         , repr_path (Filename.dirname path) program'
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
