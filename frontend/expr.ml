open Core.Std
open Int63

type op = O_Lt | O_Le | O_Eq | O_Ge | O_Gt

type op' = O'_Le | O'_Eq

type 't unop = 't -> 't

type 't binop = 't -> 't -> 't

type 't binop' = 't -> 't -> 't option

type 'l expr =
  E_True     of  'l
| E_False    of  'l
| E_Id       of  'l * string
| E_Int      of  'l * Int63.t
| E_Fn       of  'l * string * 'l expr list
| E_Not      of  'l * 'l expr
| E_And      of  'l * 'l expr * 'l expr
| E_Or       of  'l * 'l expr * 'l expr
| E_Implies  of  'l * 'l expr * 'l expr
| E_Iff      of  'l * 'l expr * 'l expr
| E_Ite      of  'l * 'l expr * 'l expr
| E_Plus     of  'l * 'l expr * 'l expr
| E_Minus    of  'l * 'l expr * 'l expr
| E_Mult     of  'l * 'l expr * 'l expr
| E_Cmp      of  'l * op * 'l expr * 'l expr

let loc_of_expr = function
  | E_True l
  | E_False l
  | E_Id (l, _)
  | E_Int (l, _)
  | E_Fn (l, _, _)
  | E_Not (l, _)
  | E_And (l, _, _)
  | E_Or (l, _, _)
  | E_Implies (l, _, _)
  | E_Iff (l, _, _)
  | E_Ite (l, _, _)
  | E_Plus (l, _, _)
  | E_Minus (l, _, _)
  | E_Mult (l, _, _)
  | E_Cmp (l, _, _, _) -> l

type ilp_type =
  T_Int of Int63.t option * Int63.t option
| T_Real of float option * float option

type result = R_Opt | R_Unbounded | R_Sat | R_Unsat | R_Unknown

type 't boption = X_True | X_False | X_Some of 't
