module type S = sig

  type ('f, 'v) term

  val (+): ('a, 'b) term -> ('a, 'b) term -> ('a, 'b) term
  val (-): ('a, 'b) term -> ('a, 'b) term -> ('a, 'b) term
  val ( * ): Core.Std.Int63.t -> ('a, 'b) term -> ('a, 'b) term

  val app : 'a -> ('a, 'b) term list -> ('a, 'b) term

  val of_int63 : Core.Std.Int63.t -> ('a, 'b) term
  val zero : ('a, 'b) term

end
