type (_, _) t

val compare :
  ('c -> 'c -> int) -> ('u -> 'u -> int) ->
  ('c, 'u) t -> ('c, 'u) t -> int

val sexp_of_t :
  ('a -> Sexplib.Sexp.t) -> ('b -> Sexplib.Sexp.t) ->
  ('a, 'b) t -> Sexplib.Sexp.t

module Box :
  Box_intf.S2 with type ('c, 's) b := ('c, 's) t

module Box_arrow :
  Box_intf.S2_arrow2 with type ('c, 's) b := ('c, 's) t

type 'i t_arrow_type =
  { a_f : 't . ('i, 't) t -> 't Lang_types.t }

module type Generators = sig
  type c
  val gen_id  : 'u Lang_types.t -> (c, 'u) t
end

module type Accessors = sig
  type c
  val type_of_t  : (c, 'u) t -> 'u Lang_types.t
  val type_of_t' : c t_arrow_type
  val compare_c : c -> c -> int
  val sexp_of_c : c -> Sexplib.Sexp.t
end

module type S = sig
  include Generators
  include Accessors with type c := c
end

module Make : functor (U : Core.Std.Unit.S) -> S
