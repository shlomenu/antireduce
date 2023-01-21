open Core

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
  Util.value_exn @@ Array.get a.contents i

let set a i v =
  assert (i < a.occupancy) ;
  Array.set a.contents i (Some v)

let rec ensure_length a l default =
  if a.occupancy >= l then () else (push a default ; ensure_length a l default)

let clear a =
  a.occupancy <- 0 ;
  a.contents <- Array.create ~len:10 None
