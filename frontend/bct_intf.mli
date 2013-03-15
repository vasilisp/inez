module type Bct_context = sig
  
  (** variables *)
  type t

  (** function identifiers *)
  type f

  (** define a variable with optional lower and upper bounds *)
  val get_t: ?lb:int -> ?ub:int -> unit

  (** [add_eq op i] enforces i = 0 *) 
  val add_eq: 't Expr.iexpr -> unit
  
  (** [add_le op i] enforces i <= 0 *) 
  val add_le: 't Expr.iexpr -> unit

  (** [add_call i f l] enforces i = f(l) *)
  val add_call: t -> f -> t Expr.offset list -> unit

end
