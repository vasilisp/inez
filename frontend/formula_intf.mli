module type S = sig

  open Terminology

  type ('f, 'v) term
  type ('f, 'v) formula

  (** term operators *)

  val (+): ('f, 'v) term binop
  val (-): ('f, 'v) term binop
  val ( * ): Core.Std.Int63.t -> ('f, 'v) term -> ('f, 'v) term
  val app: 'f -> ('f, 'v) term list -> ('f, 'v) term
  val of_int63: Core.Std.Int63.t -> ('f, 'v) term

  (** formula constants *)

  val true': ('f, 'v) formula
  val false': ('f, 'v) formula

  (** formula operators *)

  val not: ('f, 'v) formula unop
  val (&&): ('f, 'v) formula binop
  val (||): ('f, 'v) formula binop
  val (=>): ('f, 'v) formula binop
  val ite: ('f, 'v) formula ternop

  (** mixed operands *)

  val (<): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) formula
  val (<=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) formula
  val (=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) formula
  val (>=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) formula
  val (>): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) formula
  val iite:
    ('f, 'v) formula -> ('f, 'v) term -> ('f, 'v) term ->
    ('f, 'v) term

end
