module type S = sig

  open Core.Std
  open Terminology

  (** function identifiers *)
  type f

  (** context *)
  type ctx

  type var

  val get_int_var: ctx -> var

  val get_bool_var: ctx -> var

  (** assert constraint *)
  val assert_formula:
    ctx ->
    (f, var) Inez_logic.atom Formula.formula ->
    unit

  val solve: ctx -> result

  val deref: ctx -> var -> Int63.t option

end
