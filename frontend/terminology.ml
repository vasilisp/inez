type 't unop            =  't -> 't

type 't binop           =  't -> 't -> 't

type 't ternop          =  't -> 't -> 't -> 't

type op                 =  O_Lt | O_Le | O_Eq | O_Ge | O_Gt

type op'                =  O'_Le | O'_Eq
with compare, sexp

type 'v monomial        =  Core.Std.Int63.t * 'v

type 'v offset          =  'v * Core.Std.Int63.t
with compare, sexp

type 'v isum            =  'v monomial list

type 'v iexpr           =  'v isum offset

type mip_type           =  T_Int of (Core.Std.Int63.t option *
                                       Core.Std.Int63.t option)
                           | T_Real of float option * float option

type result             =  R_Opt | R_Unbounded | R_Sat
                           | R_Unsat | R_Unknown

type response           =  N_Ok | N_Unsat
with compare, sexp

type 't signed          =  S_Pos of 't | S_Neg of 't

type ('i, 'b) ibeither  =  H_Int of 'i | H_Bool of 'b
with compare, sexp
