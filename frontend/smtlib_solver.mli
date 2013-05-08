module R : sig

  type 'r t = P_Ok of 'r | P_Unsupported | P_Syntax | P_Type

  val map : 'a t -> f:('a -> 'a) -> 'a t
  val map' : 'a t -> f:('a -> 'a t) -> 'a t

end

module Make :

  functor (S : Solver_intf.S) ->
    functor (I : Lang_ids.S with type c = S.c) ->

sig

  val main :
    in_channel ->
    f:(Terminology.result option R.t -> unit) ->
    f_err:(unit -> unit) ->
    unit

end
