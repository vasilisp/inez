module type S = sig

  open Core.Std
  open Terminology

  (** context *)
  type ctx

  (** integer variable *)
  type ivar

  (** boolean variable *)
  type bvar
  
  val new_ivar: ctx -> ivar

  val new_bvar: ctx -> bvar

  (** assert constraint *)
  val assert_formula:
    ctx ->
    (bvar, ivar) Lang_abstract.atom Formula.formula ->
    unit

  val solve: ctx -> result

  val deref_int: ctx -> ivar -> Int63.t option

  val deref_bool: ctx -> bvar -> bool option

  val write_bg_ctx: ctx -> string -> unit

end
