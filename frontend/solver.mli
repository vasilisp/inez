module Make

  (S : Imt_intf.S_access)
  (I : Lang_ids.Accessors) :

sig
  type c = I.c
  include (Solver_intf.S_with_holes_creatable
           with type c := c
           and type carg := S.ctx
           and type ivar := S.ivar
           and type bvar := S.bvar)
end
