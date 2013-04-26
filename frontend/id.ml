module H = (Core.Std.Int: sig
  include Core.Std.Hashable.S_binable
  val succ: t -> t
end)

include H
