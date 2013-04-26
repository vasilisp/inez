include
  (Core.Std.Int: sig
    include Core.Std.Hashable.S_binable
    val zero: t
    val succ: t -> t
  end)
