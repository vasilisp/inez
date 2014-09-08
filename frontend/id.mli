type (_, _) t

val compare :
  ('c -> 'c -> int) -> ('u -> 'u -> int) ->
  ('c, 'u) t -> ('c, 'u) t -> int

val sexp_of_t :
  ('a -> Sexplib.Sexp.t) -> ('b -> Sexplib.Sexp.t) ->
  ('a, 'b) t -> Sexplib.Sexp.t

val type_of_t : ('c, 'u) t -> 'u Type.t

val is_int : ('c, 'u) t -> bool

val is_bool : ('c, 'u) t -> bool

type ('c1, 'c2) id_mapper = {
  f_id : 's . ('c1, 's) t -> ('c2, 's) t
}

module Box :
  Box_intf.S2 with type ('c, 's) b := ('c, 's) t

module Box_arrow :
  Box_intf.S2_arrow2 with type ('c, 's) b := ('c, 's) t

module type Generators =
  Id_intf.Generators with type ('c, 'u) t_plug := ('c, 'u) t

module type Accessors =
  Id_intf.Accessors with type ('c, 'u) t_plug := ('c, 'u) t

module type S =
  Id_intf.S with type ('c, 'u) t_plug := ('c, 'u) t

module Make () : (Id_intf.S with type ('c, 'u) t_plug := ('c, 'u) t)

module Make_mapper

  (I1 : Id_intf.S with type ('c, 'u) t_plug := ('c, 'u) t)
  (I2 : Id_intf.S with type ('c, 'u) t_plug := ('c, 'u) t) :

sig
  val f : (I1.c, 'u) t -> (I2.c, 'u) t
  val f' : (I1.c, I2.c) id_mapper
end
