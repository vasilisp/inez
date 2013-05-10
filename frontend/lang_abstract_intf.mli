module type S = sig

  open Terminology

  type ('f, 'v) term
  type ('f, 'v) atom
  
  include module type of Formula_intf

  (** LIA functions *)

  val ( + ) : ('f, 'v) term binop
  val ( - ) : ('f, 'v) term binop
  val ( * ) : Core.Std.Int63.t -> ('f, 'v) term -> ('f, 'v) term

  val of_int63: Core.Std.Int63.t -> ('f, 'v) term
  val zero: ('f, 'v) term
  val one: ('f, 'v) term

  (** LIA relations *)

  val (<): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (<=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (>=): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val (>): ('f, 'v) term -> ('f, 'v) term -> ('f, 'v) atom formula
  val iite:
    ('f, 'v) atom formula -> ('f, 'v) term -> ('f, 'v) term ->
    ('f, 'v) term

end
