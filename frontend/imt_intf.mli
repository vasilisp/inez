module type Solver = sig
  
  (** context *)
  type ctx

  (** variables *)
  type var

  (** function identifiers *)
  type f

  val new_ctx: unit -> ctx

  val new_f: ctx -> string -> int -> f

  (** define a variable with optional lower and upper bounds *)
  val new_var: ctx -> Expr.ilp_type -> var

  (** [add_eq op i] enforces i = 0 *) 
  val add_eq: ctx -> var Expr.iexpr -> unit

  (** [add_le op i] enforces i <= 0 *) 
  val add_le: ctx -> var Expr.iexpr -> unit

  (** [add_call v f l] enforces v = f(l) *)
  val add_call:
    ctx -> var Expr.offset -> f -> var Expr.offset list -> unit

  val add_objective: ctx -> var Expr.isum -> unit

  val solve: ctx -> Expr.result

  val write_ctx: ctx -> string -> unit

end
