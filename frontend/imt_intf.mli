module type S = sig

  open Core.Std
  open Terminology
  
  (** context *)
  type ctx

  (** variables *)
  type var

  (** function identifiers *)
  type f
  
  (** dummy function symbol *)
  val dummy_f: f

  val new_ctx: unit -> ctx

  val new_f: ctx -> string -> int -> f

  (** define a variable with optional lower and upper bounds *)
  val new_var: ctx -> mip_type -> var

  (** [add_eq ctx i] asserts i = 0 *) 
  val add_eq: ctx -> var iexpr -> unit

  (** [add_le ctx i] asserts i <= 0 *) 
  val add_le: ctx -> var iexpr -> unit

  (** [add_indicator ctx v i] asserts v => (i <= 0) *) 
  val add_indicator: ctx -> var signed -> var iexpr -> unit

  (** [add_clause ctx l] asserts l (viewed as a clause) *)
  val add_clause: ctx -> var signed list -> unit

  (** [add_call v f l] enforces v = f(l) *)
  val add_call:
    ctx -> var option offset -> f -> var option offset list -> unit

  val add_objective: ctx -> var isum -> unit

  val solve: ctx -> result

  val deref: ctx -> var -> Int63.t option

  val write_ctx: ctx -> string -> unit

end
