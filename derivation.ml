open Core

module T = struct
  type t =
    { terminal: Program.t
    ; nonterminals: t list
    ; nonterminal: Type.t
    ; log_likelihood: float }
  [@@deriving equal, compare, sexp_of, fields]
end

include T
include Comparator.Make (T)

let rec to_program {terminal; nonterminals; _} =
  List.fold nonterminals ~init:terminal ~f:(fun f x_tree ->
      Apply (f, to_program x_tree) )
