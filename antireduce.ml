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

let rec enumerate_terminal dsl cxt req search_points =
  match req with
  | Arrow {right; _} ->
      enumerate_terminal dsl cxt right search_points
      |> Option.value_map ~default:None ~f:(fun (b, cxt', prims') ->
             Some (PAbstraction b, cxt', prims') )
  | _ -> (
    match search_points with
    | point :: rest ->
        let rec go remaining_unified =
          let location = min (List.length remaining_unified - 1) point in
          let selected = List.nth_exn remaining_unified location in
          let unselected =
            List.filteri remaining_unified ~f:(fun i _ -> i <> location)
          in
          match
            enumerate_parameters dsl cxt selected.parameters
              (partial_of_program selected.expr)
              rest
          with
          | Some _ as r ->
              r
          | None ->
              if List.is_empty unselected then None else go unselected
        in
        go @@ unifying_primitives dsl req cxt
    | _ ->
        None )

and enumerate_parameters dsl cxt parameters f search_points =
  match parameters with
  | [] ->
      Some (f, cxt, search_points)
  | last :: [] when equal_dc_type last dsl.state_type ->
      Some (PApply (f, PIndex 0), cxt, search_points)
  | x_1_ty :: rest ->
      if parameters_length dsl parameters > List.length search_points then None
      else
        let cxt, x_1_ty = apply_context cxt x_1_ty in
        enumerate_terminal dsl cxt x_1_ty search_points
        |> Option.value_map ~default:None ~f:(fun (x_1, cxt', search_points') ->
               enumerate_parameters dsl cxt' rest
                 (PApply (f, x_1))
                 search_points' )

let commands_to_program req dsl search_points =
  if not (equal_dc_type req @@ arrow dsl.state_type dsl.state_type) then
    failwith
      "commands_to_program: requested type must be of the form: dsl.state_type \
       -> dsl.state_type" ;
  enumerate_terminal dsl empty_type_context req search_points
  |> Option.value_map ~default:None ~f:(fun (p, _, prim_indices') ->
         Some (program_of_partial p, List.length prim_indices') )

type frontier_entry = {name: string; program: program}

type 'a prededup_frontier_entry =
  {output: 'a; program_size: int; filename: string; path: string}

let verbose_duplicates m convert priority l =
  List.fold l ~init:(Hashtbl.create m) ~f:(fun tbl c ->
      Hashtbl.update tbl (convert c) ~f:(function
        | None ->
            [c]
        | Some cs ->
            List.sort (c :: cs) ~compare:priority ) ;
      tbl )
  |> Hashtbl.fold ~init:([], []) ~f:(fun ~key:_ ~data (redundant, best) ->
         (List.drop data 1 :: redundant, List.hd_exn data :: best) )

let load_frontier_from parse dir frontier =
  Array.filter_map frontier ~f:(fun filename ->
      let path = Filename.concat dir filename in
      let j = S.from_file path in
      Some (parse @@ SU.to_string @@ SU.member "original" j, path, j) )
  |> Array.to_list |> Util.unzip3

let overwrite_frontier programs' paths file_contents =
  List.zip_exn programs' file_contents
  |> List.zip_exn paths
  |> List.fold_right
       ~init:(Set.empty (module String), [])
       ~f:(fun (path, (program', file_content)) (s, l) ->
         if not (Set.mem s @@ path) then
           (Set.add s @@ path, (path, program', file_content) :: l)
         else (s, l) )
  |> snd
  |> List.map ~f:(fun (path, program', file_content) ->
         ( path
         , Util.Yojson_util.sub "original"
             (`String (string_of_program program'))
             file_content
           |> Util.Yojson_util.sub "beta_reduced"
                (`String (string_of_program @@ beta_normal_form program')) ) )
  |> List.iter ~f:(fun (path, file_content') ->
         Caml.Sys.remove path ;
         S.to_file path file_content' )

let commands_to_entry ~(default_program : program)
    ~(default_output : unit -> 'b) ~(evaluate : program -> 'a option)
    ~(postprocess_output : 'a -> 'b) ~(yojson_of_output : 'b -> S.t)
    ~(request : dc_type) ~dsl cmds =
  let translated, timed_out, p, n_unused, output =
    match commands_to_program request dsl cmds with
    | Some (p, n_unused) ->
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
    [ ("n_unused", `Int n_unused)
    ; ("translated", `Bool translated)
    ; ("timed_out", `Bool timed_out)
    ; ("beta_reduced", `String (string_of_program @@ beta_normal_form p))
    ; ("original", `String (string_of_program p))
    ; ("output", yojson_of_output output) ]

let execute_and_save ~(timeout : float) ~(attempts : int) ~dsl ~default_program
    ~default_output ~evaluate ~postprocess_output ~yojson_of_output ~request j =
  SU.member "commands" j |> SU.to_list |> List.map ~f:SU.to_int
  |> commands_to_entry ~default_program ~default_output
       ~evaluate:(evaluate ~timeout ~attempts)
       ~postprocess_output ~yojson_of_output ~request ~dsl
  |> S.to_channel Out_channel.stdout
