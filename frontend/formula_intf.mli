module type S = sig

  type ('f, 'v) term
  type ('f, 'v) formula

  (** term operators *)

  val (+): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) term
  val (-): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) term
  val ( * ): Core.Std.Int63.t -> ('f, 'v) term -> ('f, 'v) term
  val app: 'f -> ('f, 'v) term list -> ('f, 'v) term
  val of_int63: Core.Std.Int63.t -> ('f, 'v) term

  (** formula constants *)

  val true': ('f, 'v) formula
  val false': ('f, 'v) formula

  (** formula operators *)

  val not: ('f, 'v) formula -> ('f, 'v) formula
  val (&&): ('f, 'v) formula -> ('f, 'v) formula -> ('f, 'v) formula
  val (||): ('f, 'v) formula -> ('f, 'v) formula -> ('f, 'v) formula
  val (=>): ('f, 'v) formula -> ('f, 'v) formula -> ('f, 'v) formula
  val ite:
    ('f, 'v) formula -> ('f, 'v) formula -> ('f, 'v) formula ->
    ('f, 'v) formula

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
