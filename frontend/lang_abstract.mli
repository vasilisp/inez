(* atomic formulas *)

module rec A : (Lang_abstract_intf.Atom
                with type ('i, 's) m := ('i, 's) M.t)

and M : (Lang_abstract_intf.Term_with_ops
         with type 'i a = 'i A.t)

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

module Make_term (T : Core.T.T1) :
  (Lang_abstract_intf.Term_with_ops with type 'i a = 'i T.t)

module Make_term_conv
  
  (M1 : Lang_abstract_intf.Term)
  (M2 : Lang_abstract_intf.Term_with_ops) :

sig

  val map :
    ('c1, 's) M1.t ->
    f:('c1 M1.a -> 'c2 M2.a) ->
    fv:(('c1, 'c2) Lang_ids.id_mapper) ->
    ('c2, 's) M2.t

  val map_non_atomic :
    ('c1, 's) M1.t ->
    f:('c1 M1.a -> 'c2 M2.a Formula.t) ->
    fv:(('c1, 'c2) Lang_ids.id_mapper) ->
    ('c2, 's) M2.t

end
