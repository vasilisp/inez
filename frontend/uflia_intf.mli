type 't unop = 't -> 't

type 't binop = 't -> 't -> 't

type 't binop' = 't -> 't -> 't option

module type Solver = sig

  (** context *)
  type ctx

  (** function identifiers *)
  type f

  type term

  type formula

  (** boolean operators *)

  val get_not: ctx -> formula unop

  val get_and: ctx -> formula binop

  val get_or: ctx -> formula binop

  val get_implies: ctx -> formula binop

  (** term operators *)

  val get_plus: ctx -> term binop

  val get_minus: ctx -> term binop

  val get_app: ctx -> f -> term list -> term option

  val get_mult: ctx -> Int64.t -> term -> term

end
