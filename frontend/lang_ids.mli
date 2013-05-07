type ('c, 't) t

module type Generators = sig
  type c
  val gen_id  : 'u Lang_types.t -> (c, 'u) t
end

module type Accessors = sig
  type c
  val type_of_t  : (c, 'u) t -> 'u Lang_types.t
end

module type S = sig
  include Generators
  include Accessors with type c := c
end

module Make : functor (U : Core.Std.Unit.S) -> S
