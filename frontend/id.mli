type (_, _) t

val compare :
  ('c -> 'c -> int) -> ('u -> 'u -> int) ->
  ('c, 'u) t -> ('c, 'u) t -> int

type 'i t_arrow_type =
  private { a_f : 't . ('i, 't) t -> 't Type.t }

val type_of_t : ('c, 'u) t -> 'u Type.t

val is_int : ('c, 'u) t -> bool

val is_bool : ('c, 'u) t -> bool

val type_of_t' : 'i t_arrow_type

val sexp_of_t :
  ('a -> Sexplib.Sexp.t) -> ('b -> Sexplib.Sexp.t) ->
  ('a, 'b) t -> Sexplib.Sexp.t

type ('c1, 'c2) id_mapper = {
  f_id : 's . ('c1, 's) t -> ('c2, 's) t
}

module Box :
  Box_intf.S2 with type ('c, 's) b := ('c, 's) t

module Box_arrow :
  Box_intf.S2_arrow2 with type ('c, 's) b := ('c, 's) t

module type Generators = sig
  type c
  val gen_id  : 'u Type.t -> (c, 'u) t
end

module type Accessors = sig
  type c
  val type_of_t  : (c, 'u) t -> 'u Type.t
  val type_of_t' : c t_arrow_type
  val compare_c : c -> c -> int
  val sexp_of_c : c -> Sexplib.Sexp.t
end

module type S = sig
  include Generators
  include Accessors with type c := c
end

module Make (U : Core.Std.Unit.S) : S

module Make_mapper (I1 : S) (I2 : S) : sig
  val f : (I1.c, 'u) t -> (I2.c, 'u) t
  val f' : (I1.c, I2.c) id_mapper
end
