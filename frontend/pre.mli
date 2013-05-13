module Make : functor (I : Lang_ids.Accessors) -> sig

  type fun_id = I.c Lang_ids.Box_arrow.t

  type ibflat = private (term, formula) Terminology.ibeither

  and args = private ibflat list

  and app = private fun_id * args

  and sumt = private Core.Std.Int63.t * term_base

  and sum = private sumt list

  and iite = private formula * term * term

  and term_base = private
                  | B_Var   of  (I.c, int) Lang_ids.t
                  | B_App   of  app
                  | B_Ite   of  iite

  and term = private
             | G_Base  of  term_base
             | G_Sum   of  sum Terminology.offset

  and bite = private formula * formula * formula

  and formula = private
                | U_Var   of  (I.c, bool) Lang_ids.t
                | U_Atom  of  term * Terminology.op'
                | U_Not   of  formula
                | U_And   of  formula list
                | U_App   of  app
                | U_Ite   of  bite

  with compare

  type ctx

  val flatten_formula :
    ctx -> I.c Lang_abstract.A.t Formula.t -> formula

end
