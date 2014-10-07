open Core.Std
open Terminology

module type S_ivar = sig

  (** integer variable *)
  type ivar

  val compare_ivar : ivar -> ivar -> int

  val hash_ivar : ivar -> int

  val sexp_of_ivar : ivar -> Sexplib.Sexp.t

end

module type S_bvar = sig
  
  (** boolean variable *)
  type bvar

  val compare_bvar : bvar -> bvar -> int

  val hash_bvar : bvar -> int

  val sexp_of_bvar : bvar -> Sexplib.Sexp.t

end

module type S_essentials = sig

  (** context *)
  type ctx

  include S_ivar

  include S_bvar

  val ivar_of_bvar : bvar -> ivar

  val bvar_of_ivar : ivar -> bvar

end

module type S_uf = sig

  type f

  val compare_f : f -> f -> int

  val hash_f : f -> int

  val sexp_of_f : f -> Sexplib.Sexp.t

  (** dummy function symbol *)
  val dummy_f : f

end

module type S_access = sig

  include S_essentials

  include S_uf

  val new_f : ctx -> string -> int -> f

  (** define an integer variable with optional lower and upper
      bounds *)
  val new_ivar :
    ?lb          : Int63.t ->
    ?ub          : Int63.t ->
    ?implied_int : bool ->
    ctx ->
    ivar

  (** define a boolean variable *)
  val new_bvar : ctx -> bvar

  val set_ivar_priority : ctx -> ivar -> int -> unit

  val set_bvar_priority : ctx -> bvar -> int -> unit

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

  val add_diffs_disjunction :
    ctx ->
    (ivar option offset * ivar option offset) list ->
    unit    

  val add_objective : ctx -> ivar isum -> [ `Duplicate | `Ok ]

  val solve : ctx -> result

  val ideref : ctx -> ivar -> Int63.t option

  val bderef : ctx -> bvar -> bool option

  val write_ctx : ctx -> string -> unit

end

module type S_int_bounds = sig

  type ctx

  type sol

  type t

  val get_lb_local : ctx -> t -> Int63.t option
    
  val get_ub_local : ctx -> t -> Int63.t option

  val set_lb_local :
    ctx -> t -> Int63.t -> [`Infeasible | `Ok | `Tightened]

  val set_ub_local :
    ctx -> t -> Int63.t -> [`Infeasible | `Ok | `Tightened]

  val ideref_sol : ctx -> sol -> t -> Int63.t

end

module type S_dp_access_bounds = sig

  include S_essentials

  include S_int_bounds with type ctx := ctx and type t := ivar

  val bderef_local : ctx -> bvar -> bool option

  val bderef_sol : ctx -> sol -> bvar -> bool

end

module type S_dp_access = sig

  include S_dp_access_bounds

  val ibranch :
    ctx -> ivar -> float -> [`Ok | `Fail]

  val ibranch_nary :
    ctx -> ivar ->
    middle:float -> n:int -> width:float ->
    [`Ok | `Fail]

  val bbranch :
    ctx -> bvar -> [`Ok | `Fail]

end

module type S_cut_gen_access = sig

  include S_dp_access_bounds

  val add_cut_local :
    ctx -> ivar Terminology.iexpr -> [`Ok | `Unsat]

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
     with type ivar := ivar_plug
     and type bvar := bvar_plug) :

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

module type S_with_dp = sig
    
  include S_essentials
  include S_uf

  module F

    (D : S_dp
     with type ivar_plug := ivar
     and type bvar_plug := bvar) :

  sig

    include
      (S_essentials
       with type ctx = ctx
       and type ivar = ivar
       and type bvar = bvar)
      
    include
      (S_uf with type f = f)
      
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

  end

end

module type S_cut_gen = sig

  type ivar_plug
  type bvar_plug

  include Ctx_intf.S_unit_creatable

  module F

    (S : S_cut_gen_access
     with type ivar := ivar_plug
     and type bvar := bvar_plug) :

  sig

    val push_level :
      ctx -> S.ctx -> unit

    val backtrack :
      ctx -> S.ctx -> unit

    val check :
      ctx -> S.ctx -> S.sol -> bool

    val generate :
      ctx -> S.ctx -> S.sol ->
      [ `Unknown | `Sat | `Unsat_Cut_Gen | `Cutoff ]

  end

end

module type S_with_cut_gen = sig
    
  include S_essentials
  include S_uf

  type sol

  module F

    (D : S_cut_gen
     with type ivar_plug := ivar
     and type bvar_plug := bvar) :

  sig

    include
      (S_essentials
       with type ctx = ctx
       and type ivar = ivar
       and type bvar = bvar)
      
    include
      (S_uf with type f = f)
      
    include
      (S_access
       with type ctx := ctx
       and type ivar := ivar
       and type bvar := bvar
       and type f := f)

    val make_ctx : D.ctx -> ctx

  end

end

