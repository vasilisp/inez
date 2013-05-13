module type T2 = sig
  type (_, _) b
  type 'c t = Box : ('c, _) b -> 'c t
end

module type T2_arrow2 = sig
  type (_, _) b
  type 'c t = Box : ('c, _ -> _) b -> 'c t
end

module type S2 = sig

  include T2

  val compare : ('c -> 'c -> int) -> 'c t -> 'c t -> int

  val sexp_of_t : ('a -> Sexplib.Sexp.t) -> 'a t -> Sexplib.Sexp.t

end

module type S2_arrow2 = sig

  include T2_arrow2
  
  val compare :
    ('c -> 'c -> int) -> 'c t -> 'c t -> int

  val sexp_of_t :
    ('c -> Sexplib.Sexp.t) -> 'c t -> Sexplib.Sexp.t

end
