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

  type (_, _) t
  type int_plug

  val ( ~- ) : ('i, int) t -> ('i, int) t

  (* infix operators *)

  val ( + ) : ('i, int) t -> ('i, int) t -> ('i, int) t
  val ( * ) : int_plug -> ('i, int) t -> ('i, int) t
  val ( - ) : ('i, int) t -> ('i, int) t -> ('i, int) t

  (* pseudo-quantifiers *)

  val sum : 'a list -> f:('a -> ('c, int) t) -> ('c, int) t

end

module type Mixed = sig

  type (_, _) t

  type _ atom_plug

  type _ formula_plug

  (* prefix operators *)

  val iite :
    'i atom_plug formula_plug ->
    ('i, int) t -> ('i, int) t -> ('i, int) t

  (* infix operators *)

  val ( < ) :
    ('i, int) t -> ('i, int) t -> 'i atom_plug formula_plug
  val ( <= ) :
    ('i, int) t -> ('i, int) t -> 'i atom_plug formula_plug
  val ( = ) :
    ('i, int) t -> ('i, int) t -> 'i atom_plug formula_plug
  val ( >= ) :
    ('i, int) t -> ('i, int) t -> 'i atom_plug formula_plug
  val ( > ) :
    ('i, int) t -> ('i, int) t -> 'i atom_plug formula_plug

end

module type All = sig
  include Mixed
  include Int with type ('i, 's) t := ('i, 's) t
  include Prop with type 'i t := 'i formula_plug
end
