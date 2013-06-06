open Core.Std

open Db_lang_abstract_intf

module S : Schema = struct

  type _ t =
  | S_Int   :  int t
  | S_Bool  :  bool t
  | S_Pair  :  'a t * 'b t -> ('a * 'b) t

end

module rec M : (Lang_abstract_intf.Term_with_ops
                with type 'i a = 'i A.t) =
  
  Lang_abstract.Make_term(A)

and R : (Row with type ('i, 's) m := ('i, 's) M.t) = R

and D : (Db_with_ops
         with type 'i a := 'i A.t
         and type 's s := 's S.t
         and type ('i, 's) r := ('i, 's) R.t) =

struct

  type 'i a = 'i A.t
    
  type ('i, 's) r = ('i, 's) R.t

  type ('i, _) t =
  | D_Input  :  'r S.t * ('i, 'r) r list ->
    ('i, 'r) t
  | D_Cross  :  ('i, 'r) t * ('i, 's) t ->
    ('i, 'r * 's) t
  | D_Sel    :  ('i, 'r) t * (('i, 'r) r -> 'i a Formula.t) ->
    ('i, 'r) t

  let sel a f = D_Sel (a, f)

  let cross a b = D_Cross (a, b)

  let rec schema_of_t :
  type r . ('i, r) t -> r S.t =
    function
    | D_Input (s, _) ->
      s
    | D_Cross (a, b) ->
      S.S_Pair (schema_of_t a, schema_of_t b)
    | D_Sel (a, _) ->
      schema_of_t a

end

and A :

  (Atom with type ('i, 's) d := ('i, 's) D.t
        and type ('i, 's) m := ('i, 's) M.t) = A

(* I copy-pasted the module below from lang_abstract.ml . There is no
   obvious way of functorizing it, because the atoms (A) differ. *)

module Ops = struct

  type 'a formula = 'a Formula.t

  include (M : Ops_intf.Int
           with type ('i, 'q) t := ('i, 'q) M.t
           and type i := Int63.t)

  include A

  include (Formula : Ops_intf.Prop
           with type 'a t := 'a formula)

  let iite c a b = M.M_Ite (c, a, b)

  let (<) a b =
    Formula.F_Atom (A_Le (M.(a + M_Int Int63.one - b)))

  let (<=) a b =
    Formula.F_Atom (A_Le M.(a - b))

  let (=) a b =
    Formula.F_Atom (A_Eq M.(a - b))

  let (>=) a b = b <= a

  let (>) a b = b < a

end
