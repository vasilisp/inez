open Core.Std
open Terminology

module type S_access = sig

  (** context *)
  type ctx

  (** integer variable *)
  type ivar

  (** boolean variable *)
  type bvar

  (** function identifiers *)
  type f

  val compare_f : f -> f -> int

  val hash_f : f -> int

  val sexp_of_f : f -> Sexplib.Sexp.t

  val compare_ivar : ivar -> ivar -> int

  val hash_ivar : ivar -> int

  val sexp_of_ivar : ivar -> Sexplib.Sexp.t

  val compare_bvar : bvar -> bvar -> int

  val hash_bvar : bvar -> int

  val sexp_of_bvar : bvar -> Sexplib.Sexp.t

  val ivar_of_bvar : bvar -> ivar

  val bvar_of_ivar : ivar -> bvar

  (** dummy function symbol *)
  val dummy_f : f

  val new_f : ctx -> string -> int -> f

  (** define an integer variable with optional lower and upper
      bounds *)
  val new_ivar : ctx -> mip_type -> ivar

  (** define a boolean variable *)
  val new_bvar : ctx -> bvar

  (** [negate_var ctx v] = not v *)
  (* A dumb solver can implement negate_bvar by introducing a fresh
     bvar v_neg and enforcing v_neg + v = 1. SCIP can represent
     negation symbolically. We need negated variables to appear in the
     left-hand side of indicators. *)
  val negate_bvar : ctx -> bvar -> bvar

  (** [add_eq ctx i rhs] asserts i = rhs *) 
  val add_eq : ctx -> ivar isum -> Int63.t -> unit

  (** [add_le ctx i rhs] asserts i <= rhs *) 
  val add_le : ctx -> ivar isum -> Int63.t -> unit

  (** [add_indicator ctx v i] asserts v => (i <= rhs) *) 
  val add_indicator :
    ctx -> bvar signed -> ivar isum -> Int63.t -> unit

  (** [add_clause ctx l] asserts l (viewed as a clause) *)
  val add_clause : ctx -> bvar signed list -> unit

  (** [add_call v f l] enforces v = f(l) *)
  val add_call :
    ctx -> ivar option offset -> f -> ivar option offset list ->
    unit

  val add_objective : ctx -> ivar isum -> [ `Duplicate | `Ok ]

  val solve : ctx -> result

  val ideref : ctx -> ivar -> Int63.t option

  val bderef : ctx -> bvar -> bool option

  val write_ctx : ctx -> string -> unit

end

module type S = sig
  include S_access
  include (Ctx_intf.S_creatable
           with type ctx := ctx
           and type carg := unit)
end

module type S' = sig
  include S_access
  include (Ctx_intf.S_creatable with type ctx := ctx)
end

(* Higher-level functorial interface for connecting decision
   procedures. The decision procedure expects some access to the
   underlying solver, and gets it via the argument to [F]. Once we
   plug-in something that satisfies [S_dp], we get back a solver for
   ILP Modulo (T U EUF).

   This interface is a bit over-engineered as of now. Things will get
   more complicated, and it will make more sense. *)

module type S_dp = sig
    
  (* The theory solver may want to keep a reference to the low-level
     context ([X.ctx]). It doesn't have to. *)

  include S_access

  module type Dp = sig
    type ctx
    val receive : ctx -> ivar -> ivar -> Int63.t -> response
  end

  module F (Dp : Dp) : sig
    val make_ctx : Dp.ctx -> ctx
    val register : ctx -> ivar -> ivar -> unit
  end

end
