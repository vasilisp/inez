open Core.Std
open Terminology

include Formula

type _ fun_type =
| Y_Int_Arrow_Int    :  (int -> int) fun_type
| Y_Int_Arrow_Bool   :  (int -> bool) fun_type
| Y_Bool_Arrow_Int   :  (bool -> int) fun_type
| Y_Bool_Arrow_Bool  :  (bool -> bool) fun_type
| Y_Int_Arrow        :  'a fun_type -> (int -> 'a) fun_type
| Y_Bool_Arrow       :  'a fun_type -> (bool -> 'a) fun_type

type fun_type' =
| N_Int_Arrow_Int
| N_Int_Arrow_Bool
| N_Bool_Arrow_Int
| N_Bool_Arrow_Bool
| N_Int_Arrow of fun_type'
| N_Bool_Arrow of fun_type'

type ('b, 'i, _) term =
| M_Bool  :  ('b, 'i) atom formula -> ('b, 'i, bool) term
| M_Int   :  Int63.t -> ('b, 'i, int) term
| M_Ivar  :  'i -> ('b, 'i, int) term
| M_Sum   :  ('b, 'i, int) term * ('b, 'i, int) term ->
  ('b, 'i, int) term
| M_Prod  :  Int63.t * ('b, 'i, int) term -> ('b, 'i, int) term
| M_Fun   :  int * 's fun_type -> ('b, 'i, 's) term
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

(* convert fun_type to non-GADT version (for hashing purposes) *)

let rec ungadt_fun_type: type t . t fun_type -> fun_type' = function
  | Y_Int_Arrow_Int ->
    N_Int_Arrow_Int
  | Y_Int_Arrow_Bool ->
    N_Int_Arrow_Bool
  | Y_Bool_Arrow_Int ->
    N_Bool_Arrow_Int 
  | Y_Bool_Arrow_Bool ->
    N_Bool_Arrow_Bool
  | Y_Int_Arrow t ->
    N_Int_Arrow (ungadt_fun_type t)
  | Y_Bool_Arrow t ->
    N_Bool_Arrow (ungadt_fun_type t)

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
