open Core.Std

type op = O_Lt | O_Le | O_Eq | O_Ge | O_Gt

type op' = O'_Le | O'_Eq

type 'l expr =
  E_True     of  'l
| E_False    of  'l
| E_Id       of  'l * string
| E_Int      of  'l * int
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

type 't fexpr =
  F_True
| F_Ground  of  't
| F_Not     of  't fexpr
| F_And     of  't fexpr list

type 't iexpr =
  (int * 't) list * int

type ('s, 't) gexpr =
  F_Le   of  't iexpr
| F_Eq   of  't iexpr
| F_Var  of  's

type 't offset = 't * int
