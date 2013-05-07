type ('c, 't) t

type 'c t_box = Box : ('c, _) t -> 'c t_box

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
end

module type S = sig
  include Generators
  include Accessors with type c := c
end

module Make : functor (U : Core.Std.Unit.S) -> S
