open Core
open Type
open Program
open Dsl
module S = Yojson.Safe
module SU = Yojson.Safe.Util

let request_file = "request.json"

let dsl_dir = "dsls"

let transforms_dir = "discrete_representations"

type transform = {name: string; program: program}

type 'a candidate_transform =
  {output: 'a; program_size: int; filename: string; path: string}

let verbose_duplicates m convert priority l =
  let dedup =
    List.fold l ~init:(Hashtbl.create m) ~f:(fun tbl tc ->
        Hashtbl.update tbl (convert tc) ~f:(function
          | None ->
              [tc]
          | Some tcs ->
              List.sort (tc :: tcs) ~compare:priority ) ;
        tbl )
  in
  Hashtbl.fold dedup ~init:([], []) ~f:(fun ~key:_ ~data (to_discard, kept) ->
      (List.drop data 1 :: to_discard, List.hd_exn data :: kept) )

let load_request_from = Fn.compose dc_type_of_yojson S.from_file

let load_request () = load_request_from request_file

let load_dsl_from dir j =
  dsl_of_yojson @@ S.from_file @@ Filename.concat dir @@ SU.to_string
  @@ SU.member "dsl_file" j

let load_dsl = load_dsl_from dsl_dir

let load_transforms_from domain parse dir =
  Sys.readdir dir
  |> Array.filter_map ~f:(fun filename ->
         let path = Filename.concat dir filename in
         let j = S.from_file path in
         if String.(domain = SU.to_string @@ SU.member "domain" j) then
           Some (parse @@ SU.to_string @@ SU.member "program" j, path, j)
         else None )
  |> Array.to_list |> Util.unzip3

let log_dsl_to dir new_dsl_file new_dsl =
  let new_dsl_fn = Filename.concat dir new_dsl_file in
  S.to_file new_dsl_fn @@ yojson_of_dsl new_dsl

let log_dsl = log_dsl_to dsl_dir

let overwrite_transforms programs' paths transforms =
  let transforms' =
    List.zip_exn programs' transforms
    |> List.map ~f:(fun (p', transform) ->
           Util.Yojson_util.sub "program" (yojson_of_program p') transform
           |> Util.Yojson_util.sub "program_str" (`String (string_of_program p')) )
  in
  List.zip_exn paths transforms'
  |> List.iter ~f:(fun (path, transform') ->
         Sys.remove path ; S.to_file path transform' )

let commands_to_transform ~(default_program : program)
    ~(default_output : unit -> 'b) ~(evaluate : program -> 'a option)
    ~(postprocess_output : 'a -> 'b) ~(yojson_of_output : 'b -> S.t)
    ~(transform_type : dc_type) ~(domain : string) ~dsl cmds =
  let typechecked, timed_out, p, n_unused, output =
    match Commands.commands_to_program transform_type dsl cmds with
    | Some (p, n_unused) ->
        Format.eprintf "%s\n" (string_of_program @@ beta_normal_form p) ;
        Out_channel.flush stderr ;
        let timed_out, output =
          match evaluate p with
          | Some output ->
              (false, postprocess_output output)
          | None ->
              (true, default_output ())
        in
        (true, timed_out, p, n_unused, output)
    | None ->
        (false, false, default_program, List.length cmds, default_output ())
  in
  `Assoc
    [ ("domain", `String domain)
    ; ("n_unused", `Int n_unused)
    ; ("typechecked", `Bool typechecked)
    ; ("timed_out", `Bool timed_out)
    ; ("beta_reduced", `String (string_of_program @@ beta_normal_form p))
    ; ("original", `String (string_of_program p))
    ; ("output", yojson_of_output output) ]

let execute_and_save ~(timeout : float) ~(attempts : int) ~dsl ~default_program
    ~default_output ~evaluate ~postprocess_output ~yojson_of_output
    ~transform_type ~domain j =
  SU.member "commands" j |> SU.to_list |> List.map ~f:SU.to_number
  |> commands_to_transform ~default_program ~default_output
       ~evaluate:(evaluate ~timeout ~attempts)
       ~postprocess_output ~yojson_of_output ~transform_type ~domain ~dsl
  |> S.to_channel Out_channel.stdout
