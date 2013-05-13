module type Accessors = sig
  include Core.Std.Hashable.S
  include Core.Std.Sexpable.S with type t := t
end

module type Generators = sig
  type t
  val zero : t
  val succ : t -> t
end

module type Full = sig
  include Accessors
  include Generators with type t := t
end
