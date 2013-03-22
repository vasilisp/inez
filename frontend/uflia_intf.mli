type 't unop = 't -> 't

type 't binop = 't -> 't -> 't

type 't binop' = 't -> 't -> 't option

module type Solver = sig

  (** function identifiers *)
  type f

  type term

  type formula

  (** context *)
  type ctx

  (** assert constraint *)
  val assert_formula: ctx -> formula -> unit

  val solve: ctx -> Expr.result

end
