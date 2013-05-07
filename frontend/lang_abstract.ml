open Core.Std
open Terminology

include Formula

type ('i, _) term =
| M_Bool  :  'i atom formula -> ('i, bool) term
| M_Int   :  Int63.t -> ('i, int) term
| M_Sum   :  ('i, int) term * ('i, int) term ->  ('i, int) term
| M_Prod  :  Int63.t * ('i, int) term -> ('i, int) term
| M_Ite   : 'i atom formula * ('i, int) term * ('i, int) term ->
  ('i, int) term
| M_Var   :  ('i, 's) Lang_ids.t -> ('i, 's) term
| M_App   :  ('i, 'r -> 's) term * ('i, 'r) term -> ('i, 's) term

and 'i atom =
| A_Bool  of  ('i, bool) term
| A_Le    of  ('i, int) term
| A_Eq    of  ('i, int) term

(* LIA functions *)

let (+) a b =
  match a, b with
  | M_Int x, M_Int y ->
    M_Int (Int63.(+) x y)
  | M_Int x, _ when x = Int63.zero ->
    b
  | _, M_Int x when x = Int63.zero ->
    a
  | _ ->
    M_Sum (a, b)

let ( * ) c a =
  if c = Int63.zero then
    M_Int Int63.zero
  else
    M_Prod (c, a)

let (-) a b =
  match a, b with
  | M_Int x, M_Int y ->
    M_Int (Int63.(-) x y)
  | M_Int x, _ when x = Int63.zero ->
    Int63.minus_one * b
  | _, M_Int x when x = Int63.zero ->
    a
  | _ ->
    a + (Int63.minus_one * b)

(* type conversions *)

let of_int63 x = M_Int x

(* LIA constants *)

let zero = M_Int Int63.zero

let one = M_Int Int63.one

(* LIA predicates *)

let (<) a b = F_Atom (A_Le ((a + M_Int Int63.one) - b))

let (<=) a b = F_Atom (A_Le (a - b))

let (==) a b = F_Atom (A_Eq (a - b))

let (>=) a b = b <= a

let (>) a b = b < a

let iite c a b = M_Ite (c, a, b)
