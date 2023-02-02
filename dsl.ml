open Core

type t =
  { library: Dsl_entry.t list
  ; state_type: Type.t
  ; var_log_likelihood: float
  ; size: int
  ; mass: int }
[@@deriving yojson, fields]

let to_string dsl =
  Printf.sprintf "state type : %s\n" (Type.to_string dsl.state_type)
  ^ "\tt0\t$_\n"
  ^ String.concat ~sep:"\n"
      (List.map dsl.library ~f:(fun ent ->
           Type.to_string ent.ty ^ "\t" ^ ent.dc_name ) )

let of_primitives state_type primitives =
  let size = List.length primitives in
  let n_primitives = float_of_int size in
  { library=
      List.map primitives ~f:(Dsl_entry.of_primitive (log (1. /. n_primitives)))
  ; state_type
  ; var_log_likelihood= log 0.5
  ; size
  ; mass= List.reduce_exn ~f:( + ) @@ List.map primitives ~f:Program.mass }

exception DuplicatePrimitive

let of_primitives_dedup state_type primitives =
  let size =
    List.length @@ List.dedup_and_sort ~compare:Program.compare primitives
  in
  let n_primitives = float_of_int size in
  if List.length primitives = size then
    { library=
        List.map primitives
          ~f:(Dsl_entry.of_primitive (log (1. /. n_primitives)))
    ; state_type
    ; var_log_likelihood= log 0.5
    ; size
    ; mass= List.reduce_exn ~f:( + ) @@ List.map primitives ~f:Program.mass }
  else raise DuplicatePrimitive

let to_primitives dsl = List.map dsl.library ~f:Dsl_entry.to_primitive

let log_likelihood_of_entry dsl p =
  if Program.is_index p then dsl.var_log_likelihood
  else
    match
      List.filter_map dsl.library ~f:(fun ent ->
          if Program.equal p (Dsl_entry.to_primitive ent) then Some ent
          else None )
    with
    | [ent] ->
        ent.log_likelihood
    | _ :: _ as matches -> (
        let name = Program.name_of_primitive p in
        match
          List.filter_map matches ~f:(fun ent ->
              if String.(ent.stitch_name = name) then Some ent else None )
        with
        | [ent] ->
            ent.log_likelihood
        | _ :: _ as exact_matches ->
            failwith
              ( Format.sprintf
                  "log_likelihood_under_dsl: duplicate_primitives %s"
              @@ List.to_string ~f:Program.to_string
                   (p :: List.map exact_matches ~f:Dsl_entry.to_primitive) )
        | _ ->
            failwith
              ( Format.sprintf "log_likelihood_under_dsl: missing_primitive %s"
              @@ Program.to_string p ) )
    | [] ->
        failwith
          ( Format.sprintf "log_likelihood_under_dsl: missing_primitive %s"
          @@ Program.to_string p )

let rescale ~max_diff dsl =
  let lls = List.map dsl.library ~f:(fun ent -> ent.log_likelihood) in
  let n_lls, sum_lls, min_ll, max_ll =
    List.fold lls ~init:(0, 0., Float.infinity, Float.neg_infinity)
      ~f:(fun (n, tot, mn, mx) ll ->
        (n + 1, tot +. ll, Float.min mn ll, Float.max mx ll) )
  in
  let mean_ll = sum_lls /. Float.of_int n_lls in
  let unscaled_max_diff = max_ll -. min_ll in
  let unscaled_max_pos_diff, unscaled_max_neg_diff =
    (min_ll -. mean_ll, max_ll -. mean_ll)
  in
  let max_pos_diff, max_neg_diff =
    ( unscaled_max_pos_diff /. unscaled_max_diff *. max_diff
    , unscaled_max_neg_diff /. unscaled_max_diff *. max_diff )
  in
  { dsl with
    library=
      List.map lls ~f:(fun ll ->
          let unscaled_diff = ll -. mean_ll in
          mean_ll
          +.
          if Float.(unscaled_diff >= 0.) then
            unscaled_diff /. unscaled_max_pos_diff *. max_pos_diff
          else unscaled_diff /. unscaled_max_neg_diff *. max_neg_diff )
      |> List.zip_exn dsl.library
      |> List.map ~f:(fun (ent, log_likelihood) -> {ent with log_likelihood}) }
