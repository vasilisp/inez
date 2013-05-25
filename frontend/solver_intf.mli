module type S = sig

  (** context *)
  type ctx

  type c

  (** assert constraint *)
  val assert_formula :
    ctx -> c Lang_abstract.A.t Formula.t -> unit

  val solve : ctx -> Terminology.result

  val deref_int :
    ctx -> (c, int) Lang_ids.t -> Core.Std.Int63.t option

  val deref_bool :
    ctx -> (c, bool) Lang_ids.t -> bool option

  val write_bg_ctx : ctx -> string -> unit

end

module type S_creatable = sig
  include S
  include Ctx_intf.S_creatable with type ctx := ctx
end

module type S_unit_creatable = sig
  include S_creatable with type carg := unit
end

module type Dp = sig

  type ctx

  type c

  val receive :
    ctx -> (c, int) Lang_ids.t -> (c, int) Lang_ids.t ->
    Core.Std.Int63.t -> Terminology.response

end
