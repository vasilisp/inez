module Make : functor (I : Lang_ids.Accessors) -> sig

  type fun_id = I.c Lang_ids.Box_arrow.t

  type ibflat = (term, formula) Terminology.ibeither

  and args = ibflat list

  and app = fun_id * args

  and sumt = Core.Std.Int63.t * term_base

  and sum = sumt list

  and iite = formula * term * term

  and term_base = private
                  | B_Var      of  (I.c, int) Lang_ids.t
                  | B_Formula  of  formula
                  | B_App      of  app
                  | B_Ite      of  iite

  and term = private
             | G_Base  of  term_base
             | G_Sum   of  sum Terminology.offset

  and bite = formula * formula * formula

  and formula = private
                | U_Var   of  (I.c, bool) Lang_ids.t
                | U_Atom  of  term * Terminology.op'
                | U_Not   of  formula
                | U_And   of  formula list
                | U_App   of  app
                | U_Ite   of  bite

  with compare

  val hashable_sum : sum Core.Std.Hashtbl.Hashable.t
  val hashable_args : args Core.Std.Hashtbl.Hashable.t
  val hashable_iite : iite Core.Std.Hashtbl.Hashable.t
  val hashable_bite : bite Core.Std.Hashtbl.Hashable.t
  val hashable_formula : formula Core.Std.Hashtbl.Hashable.t

  type ctx

  val make_ctx : unit -> ctx

  val dummy_formula : formula

  val flatten_formula :
    ctx -> I.c Lang_abstract.A.t Formula.t -> formula

  val ff_ite : formula -> formula -> formula -> formula

end
