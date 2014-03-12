module Make

  (S : sig
    include Imt_intf.S_ivar
    include Imt_intf.S_int_bounds with type t := ivar
    val name_diff : ctx -> ivar -> ivar -> ivar option
  end) :

sig

  include (Imt_intf.S_int_bounds
           with type ctx := S.ctx
           and type sol := S.sol)

  val sexp_of_t : t -> Sexplib.Sexp.t

  val compare : t -> t -> int

  val hashable : t Core.Std.Hashtbl.Hashable.t

  val create_dvar :
    S.ctx ->
    S.ivar option Terminology.offset ->
    S.ivar option Terminology.offset ->
    t

  val get_left : S.ctx -> t -> S.ivar option Terminology.offset

  val get_right : S.ctx -> t -> S.ivar option Terminology.offset

end
