open Core

exception Unparseable of string

type stitch_program =
  | SIndex of int
  | SParam of int
  | SAbstraction of stitch_program
  | SApply of stitch_program * stitch_program
  | SPrimitive of Program.primitive
  | SInvented of Program.invention

let rec arity_of_stitch_program = function
  | SIndex _ ->
      0
  | SAbstraction b ->
      arity_of_stitch_program b
  | SApply (f, x) ->
      max (arity_of_stitch_program f) (arity_of_stitch_program x)
  | SPrimitive _ ->
      0
  | SInvented _ ->
      0
  | SParam i ->
      i + 1

let program_of_stitch_invention_body stitch_inv =
  let m =
    List.range ~start:`exclusive ~stop:`inclusive ~stride:(-1)
      (arity_of_stitch_program stitch_inv)
      0
    |> List.mapi ~f:(fun k v -> (v, k))
  in
  let rec go d : stitch_program -> Program.t = function
    | SIndex j ->
        Index j
    | SAbstraction b ->
        Abstraction (go (d + 1) b)
    | SApply (f, x) ->
        Apply (go d f, go d x)
    | SPrimitive prim ->
        Primitive prim
    | SInvented inv ->
        Invented inv
    | SParam j ->
        Index (d + List.Assoc.find_exn ~equal m j)
  in
  List.fold_right m ~init:(go 0 stitch_inv) ~f:(fun _ (e : Program.t) ->
      Abstraction e )

let rec wrap_stitch_abstractions n e =
  if n > 0 then wrap_stitch_abstractions (n - 1) (SAbstraction e) else e

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

let primitive_parser lookup_name : 'a parser =
  token
  %% fun name ->
  Option.value_map ~default:fail ~f:(fun prim -> inject prim)
  @@ lookup_name name

let variable make_index =
  constant_parser "$" %% fun _ -> number %% fun n -> inject @@ make_index n

let parameter make_parameter =
  constant_parser "#" %% fun _ -> number %% fun n -> inject @@ make_parameter n

let rec invented make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name =
  constant_parser "{"
  %% fun _ ->
  token
  %% fun name ->
  constant_parser "}"
  %% fun _ ->
  program_parser make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name
  %% fun body ->
  let ty = infer_type body in
  inject @@ make_invention name ty body

and abstraction make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name =
  (constant_parser "(lambda" <|> constant_parser "(lam")
  %% fun _ ->
  ( whitespace
  %% fun _ ->
  program_parser make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name
  %% fun b -> constant_parser ")" %% fun _ -> inject @@ make_abstraction b )
  <|> number
      %% fun n ->
      whitespace
      %% fun _ ->
      program_parser make_apply make_index make_parameter make_invention
        infer_type make_abstraction make_n_abstractions lookup_name
      %% fun b ->
      constant_parser ")" %% fun _ -> inject @@ make_n_abstractions n b

and applications make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name f_opt =
  whitespace
  %% fun _ ->
  match f_opt with
  | None ->
      program_parser make_apply make_index make_parameter make_invention
        infer_type make_abstraction make_n_abstractions lookup_name
      %% fun f ->
      applications make_apply make_index make_parameter make_invention
        infer_type make_abstraction make_n_abstractions lookup_name (Some f)
  | Some f ->
      inject f
      <|> program_parser make_apply make_index make_parameter make_invention
            infer_type make_abstraction make_n_abstractions lookup_name
          %% fun x ->
          applications make_apply make_index make_parameter make_invention
            infer_type make_abstraction make_n_abstractions lookup_name
            (Some (make_apply f x))

and application make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name =
  constant_parser "("
  %% fun _ ->
  applications make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name None
  %% fun a -> constant_parser ")" %% fun _ -> inject a

and program_parser make_apply make_index make_parameter make_invention
    infer_type make_abstraction make_n_abstractions lookup_name =
  application make_apply make_index make_parameter make_invention infer_type
    make_abstraction make_n_abstractions lookup_name
  <|> primitive_parser lookup_name
  <|> variable make_index <|> parameter make_parameter
  <|> invented make_apply make_index make_parameter make_invention infer_type
        make_abstraction make_n_abstractions lookup_name
  <|> abstraction make_apply make_index make_parameter make_invention infer_type
        make_abstraction make_n_abstractions lookup_name

let rec type_id_or_constructor_parser () =
  token
  %% fun name ->
  ( match
      parse
        ( constant_parser "t"
        %% fun _ -> number %% fun n -> inject @@ Type.Id (Int.of_string n) )
        name
    with
  | Some type_id ->
      inject type_id
  | None ->
      inject @@ Type.kind name [] )
  <|> constant_parser "("
      %% fun _ ->
      parameters_parser ()
      %% fun parameters -> inject @@ Type.kind name parameters

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
  type_signature_parser () %% fun right -> inject @@ Type.arrow left right

and type_signature_parser () =
  type_id_or_constructor_parser () <|> arrow_parser ()

let parse_program primitives s =
  parse
    (program_parser
       (fun f x -> Program.Apply (f, x))
       (fun n -> Program.Index (Int.of_string n))
       (fun _ ->
         failwith
         @@ Format.sprintf
              "parse_program: stitch parameter syntax found in program: %s" s )
       (fun name ty body -> Invented {name; ty; body})
       (fun body ->
         try Program.closed_inference body
         with e ->
           Printf.printf "Could not type check invented %s\n"
             (Program.to_string body) ;
           raise e )
       (fun b -> Abstraction b)
       (fun n b -> Program.wrap_abstractions (Int.of_string n) b)
       (Hashtbl.find primitives) )
    s

let parse_program_exn primitives s =
  match parse_program primitives s with
  | Some p ->
      p
  | None ->
      raise (Unparseable s)

let parse_stitch_invention primitives s =
  Option.map ~f:program_of_stitch_invention_body
  @@ parse
       (program_parser
          (fun f x -> SApply (f, x))
          (fun n -> SIndex (Int.of_string n))
          (fun n -> SParam (Int.of_string n))
          (fun _ _ _ ->
            failwith
            @@ Format.sprintf
                 "parse_stitch_invention: invention syntax detected: all \
                  subroutines should be referred to by name: %s"
                 s )
          (fun _ ->
            failwith
            @@ Format.sprintf
                 "parse_stitch_invention: invention syntax detected: all \
                  subroutines should be referred to be name: %s"
                 s )
          (fun b -> SAbstraction b)
          (fun n b -> wrap_stitch_abstractions (Int.of_string n) b)
          (Fn.compose
             (Option.map ~f:(function
               | Program.Primitive prim ->
                   SPrimitive prim
               | Program.Invented inv ->
                   SInvented inv
               | p ->
                   failwith
                   @@ Format.sprintf
                        "parse_program: not a base or invented primitive: %s"
                        (Program.to_string p) ) )
             (Hashtbl.find primitives) ) )
       s

let parse_stitch_invention_exn primitives s =
  match parse_stitch_invention primitives s with
  | Some inv ->
      inv
  | None ->
      raise (Unparseable s)

let parse_type_signature = parse (type_signature_parser ())
