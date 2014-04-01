module Make
  
  (Imt : Imt_intf.S_with_cut_gen)
  (I : Id.S) :

sig

  include (Solver_intf.S with type c := I.c)

  val make_ctx : unit -> ctx

  val mono_increasing : ctx -> (I.c, int -> int) Id.t -> unit

  val assert_axiom : ctx -> I.c Axiom.t -> [`Ok | `Unsupported ]

end
