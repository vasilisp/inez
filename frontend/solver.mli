module Make :
  functor (S : Imt_intf.S) ->
    functor (I : sig type c end) -> sig
      include Solver_intf.S with type c := I.c
      val make_ctx: unit -> ctx
    end


