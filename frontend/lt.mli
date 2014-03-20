module Make

  (Imt : sig

    include Imt_intf.S_essentials
      
    type sol

    module Dvars :
      (Imt_intf.Dvars_access
       with type ctx_plug := ctx
       and type sol_plug := sol)
      
  end) :

sig
  
  include (Imt_intf.S_cut_gen
           with type ivar_plug := Imt.ivar
           and type bvar_plug := Imt.bvar
           and type dvar_plug := Imt.Dvars.t)

  type axiom_id
  with compare, sexp_of

  type occ = axiom_id * Imt.Dvars.t list * int option ref

  type instantiator =
    axiom_id -> Imt.Dvars.t list -> Imt.ivar Terminology.iexpr list

  val assert_axiom :
    ctx -> instantiator -> axiom_id

  val assert_instance :
    ctx -> axiom_id -> Imt.Dvars.t list -> unit

end
