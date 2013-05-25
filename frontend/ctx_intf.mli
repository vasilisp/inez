module type S = sig
  type ctx
end

module type S_creatable = sig
  type carg
  include S
  val make_ctx : carg -> ctx
end

module type S_unit_creatable =
  S_creatable with type carg := unit
    
