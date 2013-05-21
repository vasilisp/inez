open Core.Std

open Db_lang_abstract_intf

module rec R :
  (Row with type ('i, 's) m := ('i, 's) M.t) = R

and D :
  (Db with type 'i a := 'i A.t) = D

and A :
  (Atom with type ('i, 's) d := ('i, 's) D.t
        and type ('i, 's) m := ('i, 's) M.t) = A

and M : (Lang_abstract_intf.Term_with_ops with type 'i a := 'i A.t) =
  Lang_abstract.Make_term(A)
