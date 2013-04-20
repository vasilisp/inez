open Core.Std
open Terminology

include Formula

type ('b, 'i, _) term =
| M_Bool  :  ('b, 'i) atom formula -> ('b, 'i, bool) term
| M_Int   :  Int63.t -> ('b, 'i, int) term
| M_Ivar  :  'i -> ('b, 'i, int) term
| M_Sum   :  ('b, 'i, int) term * ('b, 'i, int) term ->
  ('b, 'i, int) term
| M_Prod  :  Int63.t * ('b, 'i, int) term -> ('b, 'i, int) term
| M_Fun   :  int * 's Types.fun_type -> ('b, 'i, 's) term
| M_App   :  ('b, 'i, 'r -> 's) term * ('b, 'i, 'r) term ->
  ('b, 'i, 's) term
| M_Ite   :  ('b, 'i) atom formula *
      ('b, 'i, int) term *
      ('b, 'i, int) term -> ('b, 'i, int) term

and ('b, 'i) atom =
| A_Le    of  ('b, 'i, int) term
| A_Eq    of  ('b, 'i, int) term
| A_Bool  of  ('b, 'i, bool) term
| A_Bvar  of  'b

(* type utilities *)

let rec rightmost_ibtype_of_term :
type t . ('b, 'i, t) term -> Types.ibtype =
  function
  | M_Bool _ -> Types.E_Bool
  | M_Int _ -> Types.E_Int
  | M_Ivar _ -> Types.E_Int
  | M_Sum (_, _) -> Types.E_Int
  | M_Prod (_, _) -> Types.E_Int
  | M_Fun (_, y) -> Types.rightmost_ibtype_of_fun_type y
  | M_App (t, _) -> rightmost_ibtype_of_term t
  | M_Ite (_, _, _) -> Types.E_Int

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

let (=) a b = F_Atom (A_Eq (a - b))

let (>=) a b = b <= a

let (>) a b = b < a

let iite c a b = M_Ite (c, a, b)
