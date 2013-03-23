module type S = sig

  open Terminology

  type ('f, 'v) term
  type ('f, 'v) atom
  type 'g formula

  (** term operators *)

  val (+): ('f, 'v) term binop
  val (-): ('f, 'v) term binop
  val ( * ): Core.Std.Int63.t -> ('f, 'v) term -> ('f, 'v) term
  val app: 'f -> ('f, 'v) term list -> ('f, 'v) term
  val of_int63: Core.Std.Int63.t -> ('f, 'v) term

  (** formula constants *)

  val true': ('f, 'v) atom formula
  val false': ('f, 'v) atom formula

  (** formula operators *)

  val not: ('f, 'v) atom formula unop
  val (&&): ('f, 'v) atom formula binop
  val (||): ('f, 'v) atom formula binop
  val (=>): ('f, 'v) atom formula binop
  val ite: ('f, 'v) atom formula ternop

  (** mixed operands *)

  val (<): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (<=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (>=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (>): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val iite:
    ('f, 'v) atom formula -> ('f, 'v) term -> ('f, 'v) term ->
    ('f, 'v) term

end
