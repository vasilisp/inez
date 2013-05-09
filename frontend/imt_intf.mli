module type S = sig

  open Core.Std
  open Terminology

  (** context *)
  type ctx

  (** integer variable *)
  type ivar

  (** boolean variable *)
  type bvar

  (** function identifiers *)
  type f

  val ivar_of_bvar : bvar -> ivar

  val bvar_of_ivar : ivar -> bvar
  
  (** dummy function symbol *)
  val dummy_f : f

  val new_ctx : unit -> ctx

  val new_f : ctx -> string -> int -> f

  (** define an integer variable with optional lower and upper
      bounds *)
  val new_ivar : ctx -> mip_type -> ivar

  (** define a boolean variable *)
  val new_bvar : ctx -> bvar

  (** [negate_var ctx v] = not v *)
  val negate_bvar : ctx -> bvar -> bvar

  (** [add_eq ctx i] asserts i = 0 *) 
  val add_eq : ctx -> ivar iexpr -> unit

  (** [add_le ctx i] asserts i <= 0 *) 
  val add_le : ctx -> ivar iexpr -> unit

  (** [add_indicator ctx v i] asserts v => (i <= 0) *) 
  val add_indicator : ctx -> bvar signed -> ivar iexpr -> unit

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
