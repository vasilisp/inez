(* atomic formulas *)

module rec A : (Lang_abstract_intf.Atom
                with type ('i, 's) m := ('i, 's) M.t)

and M : (Lang_abstract_intf.Term_with_ops
         with type 'i a := 'i A.t)

(* boxed terms *)

module Box : Box_intf.T2 with type ('i, 's) b := ('i, 's) M.t

(* mostly infix operators; that's the module "logic in e" uses under
   the hood *)

module Ops :
  (Ops_intf.All
   with type ('i, 's) t := ('i, 's) M.t
   and type 'i a := 'i A.t
   and type 'a f := 'a Formula.t
   and type i := Core.Std.Int63.t)
