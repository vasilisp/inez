type ('c, 't) t

module type S = sig
  type c
  val get_fresh_id  : 'u Lang_types.t -> (c, 'u) t
end

module Make : functor (U : Core.Std.Unit.S) -> S
