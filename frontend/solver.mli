module Make: functor (S: Imt_intf.S) -> sig
  type ctx
  include Solver_intf.S with type ctx := ctx
  val make_ctx: unit -> ctx
end
