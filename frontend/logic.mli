(* atomic formulas *)

module rec A : (Logic_intf.Atom
                with type ('i, 's) term_plug := ('i, 's) M.t)

and M : (Logic_intf.Term_with_ops
         with type 'i atom = 'i A.t)

(* boxed terms *)

module Box : Box_intf.T2 with type ('i, 's) b := ('i, 's) M.t

(* mostly infix operators; that's the module "logic in e" uses under
   the hood *)

module Ops :
  (Ops_intf.All
   with type ('i, 's) t := ('i, 's) M.t
   and type 'i atom_plug := 'i A.t
   and type 'a formula_plug := 'a Formula.t
   and type int_plug := Core.Std.Int63.t)

module Make_term (T : Core.T.T1) :
  (Logic_intf.Term_with_ops with type 'i atom = 'i T.t)

module Make_term_conv
  
  (M1 : Logic_intf.Term)
  (M2 : Logic_intf.Term_with_ops) :

sig

  val map :
    ('c1, 's) M1.t ->
    f:('c1 M1.atom -> 'c2 M2.atom) ->
    fv:(('c1, 'c2) Id.id_mapper) ->
    ('c2, 's) M2.t

  val map_non_atomic :
    ('c1, 's) M1.t ->
    f:('c1 M1.atom -> 'c2 M2.atom Formula.t) ->
    fv:(('c1, 'c2) Id.id_mapper) ->
    ('c2, 's) M2.t

end
