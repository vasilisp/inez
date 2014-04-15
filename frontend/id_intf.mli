module type Accessors_untyped = sig
  include Core.Std.Hashable.S
  include Core.Std.Sexpable.S with type t := t
end

module type Generators_untyped = sig
  type t
  val zero : t
  val succ : t -> t
end

module type Full_untyped = sig
  include Accessors_untyped
  include Generators_untyped with type t := t
end

module type Generators = sig

  type ('c, 'u) t_plug

  type c

  val gen_id : 'u Type.t -> (c, 'u) t_plug

end

module type Accessors = sig

  type ('c, 'u) t_plug

  type c

  val type_of_t : (c, 'u) t_plug -> 'u Type.t

  val compare_c : c -> c -> int

  val sexp_of_c : c -> Sexplib.Sexp.t

end

module type S = sig
  include Generators
  include (Accessors
           with type ('c, 'u) t_plug := ('c, 'u) t_plug
           and type c := c)
end
