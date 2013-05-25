module Make (S : Imt_intf.S) (I : Lang_ids.Accessors) : sig
  type c = I.c
  include Solver_intf.S_creatable with type c := c
                                  and type carg := unit
end
