module type S = sig

  (** context *)
  type ctx

  type c

  (** assert constraint *)
  val assert_formula :
    ctx -> c Logic.A.t Formula.t -> unit

  val solve : ctx -> Terminology.result

  val add_objective :
    ctx -> (c, int) Logic.M.t -> [> `Duplicate | `Ok]

  val deref_int :
    ctx -> (c, int) Id.t -> Core.Std.Int63.t option

  val deref_bool :
    ctx -> (c, bool) Id.t -> bool option

  val write_bg_ctx : ctx -> string -> unit

end

module type S_with_holes = sig

  include S

  (* extensions of S that enable plugging-in theory solvers. *)

  type ivar

  type bvar

  val negate_bvar : ctx -> bvar -> bvar

  type ovar = ivar option Terminology.offset

  val compare_ovar : ovar -> ovar -> int

  val sexp_of_ovar : ovar -> Sexplib.Sexp.t

  type xvar = bvar option Terminology.signed

  val compare_xvar : xvar -> xvar -> int

  val sexp_of_xvar : xvar -> Sexplib.Sexp.t

  (* Using lazy values, because we call these functions early, i.e.,
     before the core solver is done with preprocessing. Delaying
     execution may lead to better internal encoding. *)

  val xvar_of_formula :
    ctx -> c Logic.A.t Formula.t -> xvar Lazy.t

  val xvar_of_term :
    ctx -> (c, bool) Logic.M.t -> xvar Lazy.t

  val ovar_of_term :
    ctx -> (c, int) Logic.M.t -> ovar Lazy.t

  val bvar_of_id :
    ctx -> (c, bool) Id.t -> bvar

  val bg_assert_all_cached : ctx -> unit

end

module type S_creatable = sig
  include S
  include Ctx_intf.S_creatable with type ctx := ctx
end

module type S_unit_creatable = sig
  include S_creatable with type carg := unit
end

module type S_with_holes_creatable = sig
  include S_with_holes
  include Ctx_intf.S_creatable with type ctx := ctx
end

module type S_with_holes_unit_creatable = sig
  include S_with_holes_creatable with type carg := unit
end
