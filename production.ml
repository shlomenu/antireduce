open Core

module T = struct
  type t =
    {terminal: Program.t; nonterminals: Type.t list; log_likelihood: float}
  [@@deriving equal, compare, sexp_of, fields]
end

include T
include Comparator.Make (T)
