open Core

let value_exn x = Option.value_exn x

let choose_random l =
  if not (List.is_empty l) then
    let i = Random.int @@ List.length l in
    let selected, unselected =
      List.foldi l ~init:(None, []) ~f:(fun j (selected, unselected) elt ->
          if i = j then (Some elt, unselected) else (selected, elt :: unselected) )
    in
    Some (value_exn selected, unselected)
  else None

let rec randomize l =
  choose_random l
  |> Option.value_map ~default:[] ~f:(fun (selected, unselected) ->
         selected :: randomize unselected )

(* xs in log space *)
let logsumexp xs =
  let xs_exp = List.map xs ~f:exp in
  let x_max_exp = List.reduce_exn xs_exp ~f:Float.max in
  x_max_exp
  +. ( log @@ List.reduce_exn ~f:( +. )
     @@ List.map xs_exp ~f:(fun x_exp -> exp (x_exp -. x_max_exp)) )

let minimum l ~compare ~key =
  List.map l ~f:(fun x -> (key x, x))
  |> List.reduce_exn ~f:(fun key_x key_y ->
         if compare (fst key_x) (fst key_y) <= 0 then key_x else key_y )
  |> snd

let is_valid x = (not (Float.is_nan x)) && Float.is_finite x

let is_invalid = Fn.compose not is_valid

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

exception Timeout

let run_once_for_interval (time : float) (f : unit -> 'a) : 'a option =
  let open Caml in
  let old_behavior =
    Sys.signal Sys.sigalrm @@ Sys.Signal_handle (fun _ -> raise Timeout)
  in
  let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_behavior in
  try
    ignore
      ( Core_unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= time}
        : Core_unix.interval_timer_status ) ;
    let result = f () in
    ignore
      ( Core_unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= 0.0}
        : Core_unix.interval_timer_status ) ;
    reset_sigalrm () ;
    Some result
  with
  | Timeout ->
      ignore
        ( Core_unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= 0.0}
          : Core_unix.interval_timer_status ) ;
      reset_sigalrm () ;
      None
  | e ->
      ignore
        ( Core_unix.setitimer ITIMER_REAL {it_interval= 0.0; it_value= 0.0}
          : Core_unix.interval_timer_status ) ;
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
  module T = struct
    type t = int * int [@@deriving equal, compare, sexp_of, hash, yojson]
  end

  include T
  include Comparator.Make (T)
end

module FloatPair = struct
  type t = float * float [@@deriving compare]
end
