open Core
open Type
open Program

type 'a parser = string * int -> ('a * int) list

let inject (x : 'a) : 'a parser = fun (_, n) -> [(x, n)]

let fail : 'a parser = fun _ -> []

let bind (p : 'a parser) (f : 'a -> 'b parser) : 'b parser =
 fun (s, n) ->
  p (s, n) |> List.map ~f:(fun (p_out, n') -> f p_out (s, n')) |> List.concat

let ( %% ) = bind

let ( <|> ) (p_y : 'a parser) (p_z : 'a parser) : 'a parser =
 fun x -> p_y x @ p_z x

let constant_parser (k : string) : unit parser =
 fun (s, n) ->
  let k_len = String.length k in
  let rec check n_consumed =
    if n_consumed < k_len && Char.(s.[n + n_consumed] = k.[n_consumed]) then
      check (n_consumed + 1)
    else if n_consumed = k_len then true
    else false
  in
  if n + k_len <= String.length s && check 0 then [((), n + k_len)] else []

let token_parser ?(can_be_empty = false) (permitted : char -> bool) :
    string parser =
 fun (s, n) ->
  let s_len = String.length s in
  let rec check n_consumed =
    if n + n_consumed < s_len && permitted s.[n + n_consumed] then
      s.[n + n_consumed] :: check (n_consumed + 1)
    else []
  in
  let token = String.of_char_list @@ check 0 in
  if String.length token > 0 || can_be_empty then
    [(token, n + String.length token)]
  else []

let parse (p : 'a parser) (s : string) : 'a option =
  let parses = p (s, 0) in
  let f (parse, n) = function
    | Some _ as acc ->
        acc
    | None ->
        if n = String.length s then Some parse else None
  in
  List.fold_right parses ~init:None ~f

let permitted_nonalphanumeric =
  List.mem ~equal:Char.equal
    ['_'; '-'; '?'; '/'; '.'; '*'; '\''; '+'; '>'; '<'; '@'; '|']

let token =
  let permitted c = Char.is_alphanum c || permitted_nonalphanumeric c in
  token_parser ~can_be_empty:false permitted

let whitespace = token_parser ~can_be_empty:true Char.is_whitespace

let number = token_parser Char.is_digit

let primitive_parser (primitives : (string, program) Hashtbl.t) : program parser
    =
  token
  %% fun name ->
  match Hashtbl.find primitives name with
  | Some prim ->
      inject prim
  | None ->
      fail

let variable =
  constant_parser "$"
  %% fun _ -> number %% fun n -> inject @@ Index (Int.of_string n)

let rec invented primitives =
  constant_parser "#"
  %% fun _ ->
  program_parser primitives
  %% fun p ->
  let ty =
    try closed_inference p
    with e ->
      Printf.printf "Could not type check invented %s\n" (string_of_program p) ;
      raise e
  in
  inject (Invented (ty, p))

and abstraction primitives =
  constant_parser "(lambda"
  %% fun _ ->
  ( whitespace
  %% fun _ ->
  program_parser primitives
  %% fun b -> constant_parser ")" %% fun _ -> inject (Abstraction b) )
  <|> number
      %% fun n ->
      whitespace
      %% fun _ ->
      program_parser primitives
      %% fun b ->
      constant_parser ")"
      %% fun _ -> inject (wrap_abstractions (Int.of_string n) b)

and applications primitives (f_opt : program option) =
  whitespace
  %% fun _ ->
  match f_opt with
  | None ->
      program_parser primitives %% fun f -> applications primitives (Some f)
  | Some f ->
      inject f
      <|> program_parser primitives
          %% fun x -> applications primitives (Some (Apply (f, x)))

and application primitives =
  constant_parser "("
  %% fun _ ->
  applications primitives None
  %% fun a -> constant_parser ")" %% fun _ -> inject a

and program_parser (primitives : (string, program) Hashtbl.t) : program parser =
  application primitives
  <|> primitive_parser primitives
  <|> variable <|> invented primitives <|> abstraction primitives

let rec type_id_or_constructor_parser () =
  token
  %% fun name ->
  ( match
      parse
        ( constant_parser "t"
        %% fun _ -> number %% fun n -> inject @@ Id (Int.of_string n) )
        name
    with
  | Some type_id ->
      inject type_id
  | None ->
      inject @@ kind name [] )
  <|> constant_parser "("
      %% fun _ ->
      parameters_parser () %% fun parameters -> inject @@ kind name parameters

and parameters_parser () =
  type_id_or_constructor_parser ()
  %% fun param ->
  ( constant_parser ", "
  %% fun _ -> parameters_parser () %% fun params -> inject @@ (param :: params)
  )
  <|> constant_parser ")" %% fun _ -> inject [param]

and arrow_parser () =
  ( ( constant_parser "("
    %% fun _ ->
    arrow_parser () %% fun left -> constant_parser ")" %% fun _ -> inject left
    )
  <|> type_id_or_constructor_parser () )
  %% fun left ->
  whitespace
  %% fun _ ->
  constant_parser "->"
  %% fun _ ->
  whitespace
  %% fun _ ->
  type_signature_parser () %% fun right -> inject @@ arrow left right

and type_signature_parser () =
  type_id_or_constructor_parser () <|> arrow_parser ()

let parse_program primitives = parse (program_parser primitives)

let parse_type_signature = parse (type_signature_parser ())
