open Core.Std
open Terminology

module type S_types = sig

  (** context *)
  type ctx

  (** integer variable *)
  type ivar

  (** boolean variable *)
  type bvar

  val compare_ivar : ivar -> ivar -> int

  val hash_ivar : ivar -> int

  val sexp_of_ivar : ivar -> Sexplib.Sexp.t

  val compare_bvar : bvar -> bvar -> int

  val hash_bvar : bvar -> int

  val sexp_of_bvar : bvar -> Sexplib.Sexp.t

  val ivar_of_bvar : bvar -> ivar

  val bvar_of_ivar : ivar -> bvar

end

module type S_types_uf = sig

  type f

  val compare_f : f -> f -> int

  val hash_f : f -> int

  val sexp_of_f : f -> Sexplib.Sexp.t

  (** dummy function symbol *)
  val dummy_f : f

end

module type S_access = sig

  include S_types

  include S_types_uf

  val new_f : ctx -> string -> int -> f

  (** define an integer variable with optional lower and upper
      bounds *)
  val new_ivar : ctx -> mip_type -> ivar

  (** define a boolean variable *)
  val new_bvar : ctx -> bvar

  (** [negate_bvar ctx v] = not v *)
  val negate_bvar : ctx -> bvar -> bvar

  (** [add_eq ctx i rhs] asserts i = rhs *) 
  val add_eq : ctx -> ivar isum -> Int63.t -> unit

  (** [add_le ctx i rhs] asserts i <= rhs *) 
  val add_le : ctx -> ivar isum -> Int63.t -> unit

  (** [add_indicator ctx v i] asserts v => (i <= rhs) *) 
  val add_indicator :
    ctx -> bvar signed -> ivar isum -> Int63.t -> unit

  (** [add_clause ctx l] asserts l (viewed as a clause) *)
  val add_clause : ctx -> bvar signed list -> unit

  (** [add_call v f l] enforces v = f(l) *)
  val add_call :
    ctx -> ivar option offset -> f -> ivar option offset list ->
    unit

  val add_objective : ctx -> ivar isum -> [ `Duplicate | `Ok ]

  val solve : ctx -> result

  val ideref : ctx -> ivar -> Int63.t option

  val bderef : ctx -> bvar -> bool option

  val write_ctx : ctx -> string -> unit

end

module type S_dp_access = sig

  include S_types

  val bderef_local : ctx -> bvar -> bool option

  val get_lb_local : ctx -> ivar -> Int63.t option
    
  val get_ub_local : ctx -> ivar -> Int63.t option

  val set_lb_local :
    ctx -> ivar -> Int63.t -> [`Infeasible | `Ok | `Tightened]
    
  val set_ub_local :
    ctx -> ivar -> Int63.t -> [`Infeasible | `Ok | `Tightened]

  (* maybe redundant? *)
  val name_diff :
    ctx -> ivar -> ivar -> ivar option

  val ibranch :
    ctx -> ivar -> float -> [`Ok | `Fail]

  val ibranch_nary :
    ctx -> ivar ->
    middle:float -> n:int -> width:float ->
    [`Ok | `Fail]

  val bbranch :
    ctx -> bvar -> [`Ok | `Fail]

  type sol

  val ideref_sol : ctx -> sol -> ivar -> Int63.t

  val bderef_sol : ctx -> sol -> bvar -> bool

end

module type S_unit_creatable = sig
  include S_access
  include (Ctx_intf.S_creatable
           with type ctx := ctx
           and type carg := unit)
end

module type S_creatable = sig
  include S_access
  include (Ctx_intf.S_creatable with type ctx := ctx)
end

module type S_dp = sig

  type ivar_plug
  type bvar_plug

  include Ctx_intf.S_unit_creatable

  module F

    (S : S_dp_access
     with type ivar = ivar_plug
     and type bvar = bvar_plug) :

  sig

    val push_level :
      ctx -> S.ctx -> unit

    val backtrack :
      ctx -> S.ctx -> unit

    val check :
      ctx -> S.ctx -> S.sol -> bool

    val propagate :
      ctx -> S.ctx -> response

    val branch :
      ctx -> S.ctx -> [`Ok | `Fail]

  end

end

module type S_dp_finegrained = sig

  type ivar_plug
  type bvar_plug

  include Ctx_intf.S_unit_creatable

  module F

    (S : S_dp_access
     with type ivar = ivar_plug
     and type bvar = bvar_plug) :

  sig
    
    val push_level :
      ctx -> S.ctx -> unit
    
    val backtrack :
      ctx -> S.ctx -> unit
    
    val backtrack_root :
      ctx -> S.ctx -> unit

    val check :
      ctx -> S.ctx -> S.sol -> bool

    val receive_lb :
      ctx -> S.ctx -> S.ivar -> Int63.t -> response

    val receive_ub :
      ctx -> S.ctx -> S.ivar -> Int63.t -> response

    val receive_diff :
      ctx -> S.ctx -> S.ivar -> S.ivar -> Int63.t -> response

  end

end

module type S_with_dp = sig
    
  include S_types
  include S_types_uf

  module F

    (D : S_dp
     with type ivar_plug := ivar
     and type bvar_plug := bvar) :

  sig

    include
      (S_types
       with type ctx = ctx
       and type ivar = ivar
       and type bvar = bvar)
      
    include
      (S_types_uf with type f = f)
      
    include
      (S_access
       with type ctx := ctx
       and type ivar := ivar
       and type bvar := bvar
       and type f := f)

    val register_ivar :
      ctx -> ivar -> unit

    val register_bvar :
      ctx -> bvar -> unit

    val make_ctx : D.ctx -> ctx
    val register : ctx -> ivar -> ivar -> unit

  end

end
