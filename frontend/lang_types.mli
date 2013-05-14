type ibtype = E_Int | E_Bool

val ibtype_of_sexp : Sexplib.Sexp.t -> ibtype

val sexp_of_ibtype : ibtype -> Sexplib.Sexp.t

type _ t =
| Y_Int         :  int t
| Y_Bool        :  bool t
| Y_Int_Arrow   :  'a t -> (int -> 'a) t
| Y_Bool_Arrow  :  'a t -> (bool -> 'a) t

val compare : 'a t -> 'a t -> int

val sexp_of_t : ('b -> Sexplib.Sexp.t) -> 'b t -> Sexplib.Sexp.t

val count_arrows : 'a t -> int

val t_of_app : ('a -> 'b) t -> 'a t -> 'b t

val rightmost_ibtype_of_t : 'a t -> ibtype

module Box : sig
  include Box_sig.T1 with type 'a b := 'a t
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexplib.Sexp.t
  val t_of_ibtype : ibtype -> t
end
