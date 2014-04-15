module M : sig

  type ('i, _) t =
  | M_Var  :  ('i, 's) Id.t ->
    ('i, 's) t
  | M_App  :  ('i, 'r -> 's) t * ('i, 'r) Id.t ->
    ('i, 's) t

  type 'i binding =
  [ `Int   of  ('i, int) Id.t * ('i, int) t
  | `Bool  of  ('i, bool) Id.t * ('i, bool) t
  ]

  val fun_id_of_app : ('i, 'a) t -> 'i Id.Box_arrow.t option

  val type_of_t : ('i, 'a) t -> 'a Type.t

  val id_of_t : ('a, 'b) t -> ('a, 'b) Id.t option

end

include module type of M with type ('i, 's) t = ('i, 's) M.t

module Conv 

  (I : Id.S)
  (E : Logic_intf.Term_with_ops) :

sig

  type binding =
  [ `Bool of (I.c, bool) Id.t * (I.c, bool) E.t
  | `Int of (I.c, int) Id.t * (I.c, int) E.t ]

  type rev_binding = (I.c, int) Id.t * (I.c, int) t Terminology.iexpr

  val term_of_t :
    (I.c, 'a) t -> bindings : binding list -> (I.c, 'a) E.t

  val sum_of_term :
    (I.c, int) E.t ->
    bindings : rev_binding list ->
    (((I.c, int) t Terminology.isum * Core.Std.Int63.t) *
        rev_binding list)
      option

  val t_of_term :
    (I.c, 'a) E.t ->
    bindings : rev_binding list ->
    ((I.c, 'a) t * rev_binding list) option

end

module Matching

  (E : Logic_intf.Term_with_ops) :

sig

  type 'i binding =
  [ `Bool of ('i, bool) Id.t * ('i, bool) E.t
  | `Int of ('i, int) Id.t * ('i, int) E.t ]
  
  val do_for_match :
    ('i, 'a) E.t ->
    pattern : ('i, 'b) t ->
    f       : ('i binding list -> unit) ->
    unit

end

module Linear

  (I : Id.S) :

sig

  type loc = Loc : (I.c, int) t * (I.c, int -> 's) t -> loc

  type copy = (I.c, int) Id.t * (I.c, int) Id.t

  val linearize : (I.c, 'r) t ->
    quantified : (I.c, int) Id.t list ->
    under      : (I.c, int) t ->
    map        : ((I.c, int) Id.t, loc, 'c) Core.Std.Map.t ->
    copies     : copy list ->
    (I.c, 'r) t *
      ((I.c, int) Id.t, loc, 'c) Core.Std.Map.t *
      copy list

end

module Box : sig type 'i t = Box : ('i, 'r) M.t -> 'i t end
