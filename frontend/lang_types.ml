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

type ibtype = E_Int | E_Bool

type ('i, 'b) ibeither = H_Int of 'i | H_Bool of 'b

(* convert fun_type to non-GADT version (for hashing purposes) *)

let rec ungadt_fun_type :
type t . t fun_type -> fun_type' =
  function
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

let rec rightmost_ibtype_of_fun_type :
type t . t fun_type -> ibtype =
  function
  | Y_Int_Arrow_Int -> E_Int
  | Y_Bool_Arrow_Int -> E_Int
  | Y_Int_Arrow_Bool -> E_Bool
  | Y_Bool_Arrow_Bool -> E_Bool
  | Y_Int_Arrow y -> rightmost_ibtype_of_fun_type y
  | Y_Bool_Arrow y -> rightmost_ibtype_of_fun_type y

let rec rightmost_ibtype_of_fun_type' = function
  | N_Int_Arrow_Int -> E_Int
  | N_Bool_Arrow_Int -> E_Int
  | N_Int_Arrow_Bool -> E_Bool
  | N_Bool_Arrow_Bool -> E_Bool
  | N_Int_Arrow y -> rightmost_ibtype_of_fun_type' y
  | N_Bool_Arrow y -> rightmost_ibtype_of_fun_type' y

let count_arrows' =
  let rec ca_aux acc = function
    | N_Int_Arrow_Int | N_Bool_Arrow_Bool
    | N_Int_Arrow_Bool | N_Bool_Arrow_Int ->
      1 + acc
    | N_Int_Arrow y | N_Bool_Arrow y ->
      ca_aux (1 + acc) y
  in ca_aux 0
