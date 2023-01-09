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

let typed_hole ty = Primitive {name= "UNK"; ty}

type program_navigation = Abs of dc_type | AppLeft | AppRight

type bfs_state =
  { expr: program
  ; context: type_context
  ; path: program_navigation list
  ; log_likelihood: float
  ; size: int }

module Bfs_min_heap = Containers.Heap.Make_from_compare (struct
  type t = bfs_state

  let compare (s_1 : t) (s_2 : t) =
    -Float.compare s_1.log_likelihood s_2.log_likelihood
end)

module Program_max_heap = Containers.Heap.Make_from_compare (struct
  type t = (program[@compare.ignore]) * float [@@deriving compare]
end)

let env_of_path =
  List.fold ~init:[] ~f:(fun env nav ->
      match nav with Abs ty -> ty :: env | _ -> env )

let completed {expr; path; _} =
  match expr with
  | Primitive {name= "UNK"; _} ->
      false
  | _ ->
      List.is_empty path

let new_bfs_state req =
  { expr= typed_hole req
  ; context= empty_type_context
  ; path= []
  ; log_likelihood= 0.
  ; size= 0 }

let rec type_of_hole e path =
  match (e, path) with
  | Apply (f, _), AppLeft :: rest ->
      type_of_hole f rest
  | Apply (_, x), AppRight :: rest ->
      type_of_hole x rest
  | Abstraction b, Abs _ :: rest ->
      type_of_hole b rest
  | Primitive {name= "UNK"; ty}, [] ->
      ty
  | _ ->
      failwith "typed_hole_of_path: invalid path"

let rec expand_with e v path =
  match (e, path) with
  | Apply (f, x), AppLeft :: rest ->
      Apply (expand_with f v rest, x)
  | Apply (f, x), AppRight :: rest ->
      Apply (f, expand_with x v rest)
  | Abstraction b, Abs _ :: rest ->
      Abstraction (expand_with b v rest)
  | Primitive {name= "UNK"; _}, [] ->
      v
  | _ ->
      failwith "expand_with: invalid path"

let unwind path =
  let rec go = function
    | Abs _ :: rest | AppRight :: rest ->
        go rest
    | AppLeft :: rest ->
        AppRight :: rest
    | [] ->
        []
  in
  List.rev @@ go @@ List.rev path

let expansions dsl bfs_state =
  let req = type_of_hole bfs_state.expr bfs_state.path in
  let cxt = bfs_state.context in
  let cxt, req = apply_context cxt req in
  match req with
  | Arrow {left; right; _} ->
      [ { bfs_state with
          expr=
            expand_with bfs_state.expr
              (Abstraction (typed_hole right))
              bfs_state.path
        ; path= bfs_state.path @ [Abs left]
        ; context= cxt } ]
  | _ ->
      let env = env_of_path bfs_state.path in
      unifying_expressions dsl env req cxt
      |> Util.randomize
      |> List.map ~f:(fun unified ->
             let expr, path =
               match unified.parameters with
               | [] ->
                   ( expand_with bfs_state.expr unified.expr bfs_state.path
                   , unwind bfs_state.path )
               | _ :: rest ->
                   let app =
                     List.fold unified.parameters ~init:unified.expr
                       ~f:(fun e x_ty -> Apply (e, typed_hole x_ty))
                   in
                   ( expand_with bfs_state.expr app bfs_state.path
                   , bfs_state.path
                     @ List.map rest ~f:(fun _ -> AppLeft)
                     @ [AppRight] )
             in
             { expr
             ; path
             ; context= unified.context
             ; log_likelihood=
                 bfs_state.log_likelihood +. unified.log_likelihood
             ; size= bfs_state.size + 1 } )

let bfs ~lower_bound ~upper_bound ~max_enumerated ~end_time dsl req =
  let lower_bound, upper_bound =
    (-.Float.abs lower_bound, -.Float.abs upper_bound)
  in
  let complete = ref [] in
  let heap = ref @@ Bfs_min_heap.of_list [new_bfs_state req] in
  while
    Bfs_min_heap.size !heap > 0
    && Bfs_min_heap.size !heap < max_enumerated
    && Float.(Core_unix.time () < end_time)
  do
    let heap', best = Bfs_min_heap.take_exn !heap in
    heap := heap' ;
    assert (not (completed best)) ;
    expansions dsl best
    |> List.iter ~f:(fun successor ->
           if completed successor then (
             if
               Float.(upper_bound < successor.log_likelihood)
               && Float.(successor.log_likelihood <= lower_bound)
             then complete := successor :: !complete )
           else if Float.(upper_bound < successor.log_likelihood) then
             heap := Bfs_min_heap.add !heap successor )
  done ;
  while Bfs_min_heap.size !heap > max_enumerated do
    heap := fst @@ Bfs_min_heap.take_exn !heap
  done ;
  (!complete, Bfs_min_heap.to_list !heap)

let rec parameters_length_aux dsl len = function
  | [] ->
      len
  | last :: [] when equal_dc_type last dsl.state_type ->
      len
  | _ :: rest ->
      parameters_length_aux dsl (len + 1) rest

let parameters_length dsl = parameters_length_aux dsl 0

let rec dfs_function ~lower_bound ~upper_bound ~log_likelihood
    ?(max_size = 10000) ?(size = 0) ~end_time ?(exec = List.return) dsl env cxt
    req =
  if
    Float.(Core_unix.time () < end_time)
    && Float.(upper_bound < log_likelihood)
    && size < max_size
  then
    match req with
    | Arrow {left; right; _} ->
        dfs_function ~lower_bound ~upper_bound ~log_likelihood ~size ~end_time
          dsl (left :: env) cxt right
          ~exec:(fun (b, output, cxt', log_likelihood', size') ->
            exec (Abstraction b, output, cxt', log_likelihood', size') )
    | _ ->
        unifying_expressions dsl env req cxt
        |> Util.randomize
        |> List.concat_map ~f:(fun (selected : unifying_expression) ->
               dfs_arguments ~lower_bound ~upper_bound
                 ~log_likelihood:(log_likelihood +. selected.log_likelihood)
                 ~size:(size + 1) ~end_time
                 ~exec:(fun (p, output, cxt', log_likelihood', size') ->
                   exec
                     ( p
                     , output
                     , cxt'
                     , log_likelihood' +. selected.log_likelihood
                     , size' + 1 ) )
                 dsl env selected.context selected.parameters selected.expr )
  else []

and dfs_arguments ~lower_bound ~upper_bound ~log_likelihood ?(max_size = 9999)
    ~size ~end_time ?(exec = List.return) dsl env cxt parameters f =
  if
    Float.(Core_unix.time () < end_time)
    && Float.(upper_bound < log_likelihood)
    && size < max_size
  then
    match parameters with
    | [] ->
        if Float.(log_likelihood <= lower_bound) then exec (f, None, cxt, 0., 0)
        else []
    | x_ty :: rest ->
        if parameters_length dsl parameters <= max_size - (size + 1) then
          let cxt, x_ty = apply_context cxt x_ty in
          dfs_function ~lower_bound:0. ~upper_bound ~log_likelihood ~size
            ~end_time dsl env cxt x_ty
            ~exec:(fun (x, _, cxt', log_likelihood', size') ->
              List.concat_map ~f:exec
              @@ dfs_arguments ~lower_bound ~upper_bound
                   ~log_likelihood:(log_likelihood +. log_likelihood')
                   ~size:(size + size') ~end_time dsl env cxt' rest
                   (Apply (f, x))
                   ~exec:(fun (xs, output, cxt'', log_likelihood'', size'') ->
                     [ ( xs
                       , output
                       , cxt''
                       , log_likelihood' +. log_likelihood''
                       , size' + size'' ) ] ) )
        else []
  else []

let rec has_typed_hole = function
  | Abstraction b ->
      has_typed_hole b
  | Apply (f, x) ->
      has_typed_hole f || has_typed_hole x
  | Primitive {name= "UNK"; _} ->
      true
  | _ ->
      false

let rec dfs_holes ~lower_bound ~upper_bound ~log_likelihood ?(max_size = 10000)
    ?(size = 0) ~end_time ?(exec = List.return) dsl cxt abstraction_depth env e
    =
  if
    Float.(Core_unix.time () < end_time)
    && Float.(upper_bound < log_likelihood)
    && size < max_size
  then
    match e with
    | Abstraction b ->
        dfs_holes ~lower_bound ~upper_bound ~log_likelihood ~max_size ~size
          ~end_time dsl cxt (abstraction_depth + 1) env b
          ~exec:(fun (b', output, cxt', log_likelihood', size') ->
            exec (Abstraction b', output, cxt', log_likelihood', size') )
    | Apply (f, x) when (not (has_typed_hole f)) && has_typed_hole x ->
        dfs_holes ~lower_bound ~upper_bound ~log_likelihood ~max_size ~size
          ~end_time dsl cxt abstraction_depth env x
          ~exec:(fun (x', output, cxt', log_likelihood', size') ->
            exec (Apply (f, x'), output, cxt', log_likelihood', size') )
    | Apply (f, x) when has_typed_hole f && has_typed_hole x ->
        dfs_holes ~lower_bound ~upper_bound ~log_likelihood ~max_size ~size
          ~end_time dsl cxt abstraction_depth env f
          ~exec:(fun (f', _, cxt', log_likelihood', size') ->
            List.concat_map ~f:exec
            @@ dfs_holes ~lower_bound:0. ~upper_bound
                 ~log_likelihood:(log_likelihood +. log_likelihood')
                 ~max_size ~size:(size + size') ~end_time dsl cxt'
                 abstraction_depth env x
                 ~exec:(fun (x', output', cxt'', log_likelihood'', size'') ->
                   [ ( Apply (f', x')
                     , output'
                     , cxt''
                     , log_likelihood' +. log_likelihood''
                     , size' + size'' ) ] ) )
    | Apply (f, x) when (not (has_typed_hole f)) && not (has_typed_hole x) ->
        failwith
          "dfs_holes: recursed on branch of expression with no typed holes"
    | Apply _ ->
        failwith
          "dfs_holes: function of application has typed hole when argument \
           does not"
    | Primitive {name= "UNK"; ty= req} ->
        let env' = List.drop env (List.length env - abstraction_depth) in
        let cxt, req = apply_context cxt req in
        dfs_function ~lower_bound ~upper_bound ~log_likelihood ~max_size ~size
          ~exec ~end_time dsl env' cxt req
    | _ ->
        failwith "dfs_holes: reached leaf node that is not a typed hole"
  else []

let resume_dfs ~lower_bound ~upper_bound ?(max_size = 10000)
    ?(exec = List.return) ~end_time dsl bfs_state =
  let lower_bound, upper_bound =
    (-.Float.abs lower_bound, -.Float.abs upper_bound)
  in
  dfs_holes ~lower_bound ~upper_bound ~log_likelihood:bfs_state.log_likelihood
    ~max_size ~size:bfs_state.size ~end_time dsl bfs_state.context 0
    (env_of_path bfs_state.path) bfs_state.expr
    ~exec:(fun (p, output, cxt', log_likelihood', size') ->
      exec
        ( p
        , output
        , cxt'
        , log_likelihood' +. bfs_state.log_likelihood
        , size' + bfs_state.size ) )

let explore ~exploration_timeout ~eval_timeout ~attempts ~dsl
    ~representations_dir ~lower_bound ~upper_bound ~interval_size
    ~max_enumerated_bfs ~max_enumerated_dfs ~apply_to_state ~evaluate
    ~retrieve_result ~nontrivial ~parse ~request ~yojson_of_output
    ~key_of_output ~yojson_of_key ~key_of_yojson key_module =
  assert (
    Float.(lower_bound >= 0.)
    && Float.(lower_bound < upper_bound)
    && Float.(interval_size > 0.) ) ;
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
  Random.self_init () ;
  let end_time = Core_unix.time () +. exploration_timeout in
  let rec enumerate ~lb =
    let ub = lb +. interval_size in
    if Float.(Core_unix.time () < end_time) && Float.(ub < upper_bound) then (
      let bfs_complete, bfs_incomplete =
        bfs ~lower_bound:lb ~upper_bound:ub ~max_enumerated:max_enumerated_bfs
          ~end_time dsl request
      in
      let dfs_complete =
        List.fold bfs_incomplete ~init:Program_max_heap.empty
          ~f:(fun heap bfs_state ->
            resume_dfs ~lower_bound:lb ~upper_bound:ub ~end_time dsl bfs_state
            |> List.fold ~init:heap ~f:(fun heap (p, _, _, log_likelihood, _) ->
                   let heap' = Program_max_heap.add heap (p, log_likelihood) in
                   if Program_max_heap.size heap' > max_enumerated_dfs then
                     fst @@ Program_max_heap.take_exn heap'
                   else heap' ) )
        |> Program_max_heap.to_list |> List.map ~f:fst
      in
      List.map bfs_complete ~f:(fun bfs_state -> bfs_state.expr)
      |> ( @ ) dfs_complete
      |> List.filter_map ~f:(fun p ->
             let p_applied = apply_to_state p in
             generic_expr_of_program dsl.state_type p_applied
             |> evaluate ~timeout:eval_timeout ~attempts p_applied
             |> Option.map ~f:retrieve_result
             |> Option.bind ~f:(fun o ->
                    if nontrivial o then Some (p, o) else None ) )
      |> List.iter ~f:(fun (p, o) ->
             Hashtbl.update representations (key_of_output o) ~f:(function
               | None ->
                   (Some p, None, yojson_of_output o)
               | Some (None, None, _) ->
                   failwith "unpopulated entry"
               | Some (None, (Some prev_p as prev_best), o) ->
                   let cur_best =
                     if mass_of_program p < mass_of_program prev_p then Some p
                     else None
                   in
                   (cur_best, prev_best, o)
               | Some ((Some cur_p as cur_best), prev_best, o) ->
                   let cur_best =
                     if mass_of_program p < mass_of_program cur_p then Some p
                     else cur_best
                   in
                   (cur_best, prev_best, o) ) ) ;
      enumerate ~lb:ub )
    else ub
  in
  let max_dl = enumerate ~lb:lower_bound in
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
      ; ("cur_files", yojson_of_list yojson_of_string cur_files)
      ; ("max_dl", `Float max_dl) ] )

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
