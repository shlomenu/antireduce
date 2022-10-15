open Core

let rec unzip3 ?(unzipped = ([], [], [])) = function
  | (x, y, z) :: rest ->
      let xs, ys, zs = unzipped in
      unzip3 ~unzipped:(x :: xs, y :: ys, z :: zs) rest
  | [] ->
      unzipped

let value_exn x = Option.value_exn x

let singleton_list = function [x] -> x | _ -> assert false

(* vector operations *)

let fold1 f l = List.fold_right ~init:(List.hd_exn l) ~f (List.tl_exn l)

let minimum_by l ~compare ~f =
  List.reduce_exn l ~f:(fun x y -> if compare (f x) (f y) <= 0 then x else y)

let is_valid x = (not (Float.is_nan x)) && Float.is_finite x

let is_invalid = Fn.compose not is_valid

let lse x y =
  if is_invalid x then y
  else if is_invalid y then x
  else if Float.(x > y) then x +. log (1.0 +. exp (y -. x))
  else y +. log (1.0 +. exp (x -. y))

let softMax = lse

let lse_list (l : float list) : float =
  List.fold_left l ~f:lse ~init:Float.neg_infinity

let range = List.range 0

let flush_all () = Out_channel.flush stdout ; Out_channel.flush stderr

let time_it ?(verbose = true) description callback =
  let start_time = Time.now () in
  let return_value = callback () in
  if verbose then (
    Printf.eprintf "%s in %s.\n" description
      (Time.diff (Time.now ()) start_time |> Time.Span.to_string) ;
    flush_all () ) ;
  return_value

type progress_bar = {maximum_progress: int; mutable current_progress: int}

let make_progress_bar number_jobs =
  {maximum_progress= number_jobs; current_progress= 0}

let update_progress_bar bar new_progress =
  let max = Float.of_int bar.maximum_progress in
  let old_dots =
    Int.of_float @@ (Float.of_int bar.current_progress *. 80.0 /. max)
  in
  let new_dots = Int.of_float @@ (Float.of_int new_progress *. 80.0 /. max) in
  bar.current_progress <- new_progress ;
  if new_dots > old_dots then
    for _ = 1 to min 80 (new_dots - old_dots) do
      Out_channel.output_char stdout '.' ;
      Out_channel.flush stdout
    done

module Yojson_util = struct
  let yojson_of_hashtbl yojson_of_key yojson_of_val htbl =
    let coll ~key:k ~data:v acc =
      `List [yojson_of_key k; yojson_of_val v] :: acc
    in
    `List (Hashtbl.fold htbl ~init:[] ~f:coll)

  let hashtbl_of_yojson m key_of_yojson val_of_yojson yojson =
    match yojson with
    | `List l ->
        let htbl = Hashtbl.create m in
        let f = function
          | `List [k_yojson; v_yojson] ->
              Hashtbl.add_exn htbl ~key:(key_of_yojson k_yojson)
                ~data:(val_of_yojson v_yojson)
          | _ ->
              failwith "hashtbl_of_yojson: tuple list needed"
        in
        List.iter l ~f ; htbl
    | _ ->
        failwith "hashtbl_of_yojson: list needed"

  let sub name' value' = function
    | `Assoc attrs ->
        `Assoc
          (List.map attrs ~f:(fun (name, value) ->
               if String.(name = name') then (name, value') else (name, value) )
          )
    | _ ->
        failwith "can only sub keys of JSON object"
end

exception Timeout

let run_once_for_interval (time : float) (f : unit -> 'a) : 'a option =
  let open Caml in
  let old_behavior =
    Sys.signal Sys.sigalrm @@ Sys.Signal_handle (fun _ -> raise Timeout)
  in
  let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_behavior in
  try
    ignore
      ( Unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= time}
        : Unix.interval_timer_status ) ;
    let result = f () in
    ignore
      ( Unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= 0.0}
        : Unix.interval_timer_status ) ;
    reset_sigalrm () ;
    Some result
  with
  | Timeout ->
      ignore
        ( Unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= 0.0}
          : Unix.interval_timer_status ) ;
      reset_sigalrm () ;
      None
  | e ->
      ignore
        ( Unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= 0.0}
          : Unix.interval_timer_status ) ;
      reset_sigalrm () ;
      raise e

let rec run_for_interval ?(attempts = 1) dt f =
  if attempts < 1 then None
  else
    match run_once_for_interval dt f with
    | Some v ->
        Some v
    | None ->
        run_for_interval ~attempts:(attempts - 1) dt f

module IntPair = struct
  type t = int * int [@@deriving equal, compare, sexp_of, hash]
end

module OrdIntPair = struct
  include IntPair
  include Comparator.Make (IntPair)
end

module Array_list = struct
  type 'a t = {mutable occupancy: int; mutable contents: 'a option Array.t}

  let create () = {occupancy= 0; contents= Array.create ~len:10 None}

  let push a x =
    let l = Array.length a.contents in
    if a.occupancy >= l then (
      let n = Array.create ~len:(l * 2) None in
      Array.blito ~src:a.contents ~dst:n () ;
      a.contents <- n )
    else () ;
    Array.set a.contents a.occupancy (Some x) ;
    a.occupancy <- a.occupancy + 1

  let get a i =
    assert (i < a.occupancy) ;
    value_exn @@ Array.get a.contents i

  let set a i v =
    assert (i < a.occupancy) ;
    Array.set a.contents i (Some v)

  let rec ensure_length a l default =
    if a.occupancy >= l then ()
    else (push a default ; ensure_length a l default)

  let clear a =
    a.occupancy <- 0 ;
    a.contents <- Array.create ~len:10 None
end
