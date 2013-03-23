open Core.Std

module Make (S: Imt_intf.S) = struct

  open Formula

  type var = S.var

  type f = S.f

  type term = (f, var) Term.term

  type atom = term * Expr.op' option

  type formula = atom Formula.formula

  (*
  
    type 't offset = 't * Int63.t

    type 't isum = (Int63.t * 't) list

    type 't iexpr = 't isum offset

  *)

  type ctx =
    {r_ctx   : S.ctx;
     r_var_m : (var Expr.boption, term) Hashtbl.Poly.t;
     r_q     : formula Dequeue.t}

  (* blasting *)

  let blast_atom r = function
    | t, Some op ->
      Expr.X_True
    | t, None ->
      Expr.X_True

  let blast_formula r = function
    | F_True ->
      Expr.X_True
    | _ ->
      Expr.X_False

  let assert_formula {r_q} =
    Dequeue.push_back r_q

  let solve ({r_q} as r) =
    Dequeue.iter r_q ~f:(Fn.compose ignore (blast_formula r));
    Dequeue.clear r_q;
    Expr.R_Sat

end
