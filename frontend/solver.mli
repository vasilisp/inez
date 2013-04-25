module Make: functor (S: Imt_intf.S) -> sig
  include Solver_intf.S
  val make_ctx: unit -> ctx
end
