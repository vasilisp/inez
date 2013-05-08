module Make :
  functor (S : Imt_intf.S) ->
    functor (I : Lang_ids.Accessors) -> sig
      type c = I.c
      include Solver_intf.S with type c := c
    end
