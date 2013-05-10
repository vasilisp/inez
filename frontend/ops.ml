module type Propositional = sig

  type _ t

  val not : 'a t -> 'a t
  val (&&) : 'a t -> 'a t -> 'a t
  val (||) : 'a t -> 'a t -> 'a t
  val (=>) : 'a t -> 'a t -> 'a t

  val ite : 'a t -> 'a t -> 'a t -> 'a t

  val forall : 'a list -> f:('a -> 'b t) -> 'b t
  val forall_pairs : 'a list -> f:('a -> 'a -> 'b t) -> 'b t
  val exists : 'a list -> f:('a -> 'b t) -> 'b t

end

module type Functions = sig
    
  type ('i, _) t

  type _ a

  (* infix operators *)

  val ( + ) : ('i, int) t -> ('i, int) t -> ('i, int) t
  val ( * ) : Core.Std.Int63.t -> ('i, int) t -> ('i, int) t
  val ( - ) : ('i, int) t -> ('i, int) t -> ('i, int) t

  (* ITE not really a function *)
  
  val iite :
    'i a Formula.t -> ('i, int) t -> ('i, int) t -> ('i, int) t

end

module type Predicates = sig

  type (_, _) t

  type _ a

  val ( < ) : ('i, int) t -> ('i, int) t -> 'i a Formula.t
  val ( <= ) : ('i, int) t -> ('i, int) t -> 'i a Formula.t
  val ( == ) : ('i, int) t -> ('i, int) t -> 'i a Formula.t
  val ( >= ) : ('i, int) t -> ('i, int) t -> 'i a Formula.t
  val ( > ) : ('i, int) t -> ('i, int) t -> 'i a Formula.t

end
