open Core.Std

type ('f, 'v) term =
  M_Var   of  'v
| M_Int   of  Int63.t
| M_App   of  'f * ('f, 'v) term list
| M_Sum   of  ('f, 'v) term * ('f, 'v) term
| M_Prod  of  Int63.t * ('f, 'v) term
| M_Ite   of  ('f, 'v) formula * ('f, 'v) term * ('f, 'v) term

and ('f, 'v) formula =
  F_True
| F_Ground  of  ('f, 'v) term * Expr.op' option
| F_Not     of  ('f, 'v) formula
| F_And     of  ('f, 'v) formula * ('f, 'v) formula
| F_Ite     of  ('f, 'v) formula * ('f, 'v) formula * ('f, 'v) formula

(* term operators *)

let rec (+) a b =
  match a, b with
  | M_Int x, M_Int y ->
    M_Int (Int63.(+) x y)
  | M_Int x, _ when x = Int63.zero ->
    b
  | _, M_Int x when x = Int63.zero ->
    a
  | _ ->
    M_Sum (a, b)

let rec ( * ) c a =
  if c = Int63.zero then
    M_Int Int63.zero
  else
    M_Prod (c, a)

let rec (-) a b =
  match a, b with
  | M_Int x, M_Int y ->
    M_Int (Int63.(-) x y)
  | M_Int x, _ when x = Int63.zero ->
    Int63.minus_one * b
  | _, M_Int x when x = Int63.zero ->
    a
  | _ ->
    a + (Int63.minus_one * b)

let app f l = M_App (f, l)

let of_int63 x = M_Int x

let zero = M_Int Int63.zero

let one = M_Int Int63.one

(* constant formulas *)

let true' = F_True

let false' = F_Not F_True

(* formula operators *)

let not g = F_Not g

let (&&) g h = F_And (g, h)

let (||) g h = not (not g && not h)

let (=>) g h = not g || h

let ite c g h = F_Ite (c, g, h)

let (<) a b = F_Ground ((a + M_Int Int63.one) - b, Some Expr.O'_Le)

let (<=) a b = F_Ground (a - b, Some Expr.O'_Le)

let (=) a b = F_Ground (a - b, Some Expr.O'_Eq)

let (>=) a b = F_Ground (b - a, Some Expr.O'_Le)

let (>) a b = F_Ground ((b + M_Int Int63.one) - a, Some Expr.O'_Le)

let iite c a b = M_Ite (c, a, b)
