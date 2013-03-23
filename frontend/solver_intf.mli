module type S = sig

  open Terminology

  (** function identifiers *)
  type f

  type term

  type formula

  (** context *)
  type ctx

  (** assert constraint *)
  val assert_formula: ctx -> formula -> unit

  val solve: ctx -> result

end
