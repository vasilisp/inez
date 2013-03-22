open Core.Std

type 't offset = 't * Int63.t

type 't isum = (Int63.t * 't) list

type 't iexpr = 't isum offset

type ('f, 'v) term =
  M_Var   of  'v
| M_Int   of  Int63.t
| M_App   of  'f * ('f, 'v) term list
| M_Sum   of  ('f, 'v) term * ('f, 'v) term
| M_Prod  of  Int63.t * ('f, 'v) term

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
