module type Prop = sig

  type _ t

  (* prefix operators *)

  val not : 'a t -> 'a t
  val ite : 'a t -> 'a t -> 'a t -> 'a t

  (* infix operators *)

  val ( && ) : 'a t -> 'a t -> 'a t
  val ( || ) : 'a t -> 'a t -> 'a t
  val ( => ) : 'a t -> 'a t -> 'a t

  (* pseudo-quantifiers *)

  val forall : 'a list -> f:('a -> 'b t) -> 'b t
  val forall_pairs : 'a list -> f:('a -> 'a -> 'b t) -> 'b t
  val exists : 'a list -> f:('a -> 'b t) -> 'b t

end

module type Int = sig
    
  type ('i, _) t
  type i

  (* infix operators *)

  val ( + ) : ('i, int) t -> ('i, int) t -> ('i, int) t
  val ( * ) : i -> ('i, int) t -> ('i, int) t
  val ( - ) : ('i, int) t -> ('i, int) t -> ('i, int) t

end

module type Mixed = sig

  type (_, _) t

  type _ a

  type _ f

  (* prefix operators *)

  val iite :
    'i a f -> ('i, int) t -> ('i, int) t -> ('i, int) t

  (* infix operators *)

  val ( < ) : ('i, int) t -> ('i, int) t -> 'i a f
  val ( <= ) : ('i, int) t -> ('i, int) t -> 'i a f
  val ( == ) : ('i, int) t -> ('i, int) t -> 'i a f
  val ( >= ) : ('i, int) t -> ('i, int) t -> 'i a f
  val ( > ) : ('i, int) t -> ('i, int) t -> 'i a f

end

module type All = sig
  include Mixed
  include Int with type ('i, 's) t := ('i, 's) t
  include Prop with type 'a t := 'a f
end
