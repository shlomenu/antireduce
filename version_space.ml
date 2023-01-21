open Core

type t =
  | Union of int list
  | ApplySpace of int * int
  | AbstractionSpace of int
  | IndexSpace of int
  | TerminalSpace of Program.t
  | Universe
  | Void
[@@deriving equal, compare, sexp_of, hash]
