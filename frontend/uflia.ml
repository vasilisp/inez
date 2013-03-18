module Make (S: Imt_intf.Solver) = struct

  type var = S.var

  type f = S.f

  type ctx = {c_ctx: S.ctx}

  type term =
    M_Var of var
  | M_App of f * term list
  | M_Off of term * Int64.t
  | M_Sum of term Expr.isum

  type atom = term * Expr.op' option

  type formula = atom Expr.fexpr

  let get_and _ _ _ = Expr.F_True

  let get_or _ _ _ = Expr.F_True

  let get_not _ _ = Expr.F_True

  let get_implies _ _ _ = Expr.F_True

  let get_dummy_term {c_ctx} =
    M_App (S.new_f c_ctx "__dummy" 0, [])

  let get_plus r _ _ = get_dummy_term r

  let get_minus r _ _ = get_dummy_term r

  let get_mult r _ _ = get_dummy_term r

  let get_app r _ _ = Some (get_dummy_term r)

end
