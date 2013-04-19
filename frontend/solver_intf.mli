module type S = sig

  open Core.Std
  open Terminology

  (** function identifiers *)
  type f

  (** context *)
  type ctx

  (** integer variable *)
  type ivar

  (** boolean variable *)
  type bvar
  
  val get_ivar: ctx -> ivar

  val get_bvar: ctx -> bvar

  (** assert constraint *)
  val assert_formula:
    ctx ->
    (bvar, ivar) Lang_abstract.atom Formula.formula ->
    unit

  val solve: ctx -> result

  val deref_int: ctx -> ivar -> Int63.t option

  val deref_bool: ctx -> bvar -> bool option

end
