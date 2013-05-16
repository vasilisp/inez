module Make (S : Imt_intf.S) (I : Lang_ids.Accessors) : sig
  type c = I.c
  include Solver_intf.S with type c := c
end
