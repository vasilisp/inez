module Make (S: Imt_intf.S) = struct

  open Core.Std
  open Terminology

  type var = S.var

  type f = S.f

  type term = (f, var) Inez_logic.term

  type formula = (f, var) Inez_logic.atom Formula.formula

  type ctx =
    {r_ctx   : S.ctx;
     r_var_m : (var boption, term) Hashtbl.Poly.t;
     r_q     : formula Dequeue.t}

  (* blasting *)

  let xnot = function
    | X_True ->
      X_False
    | X_False ->
      X_True
    | X_Pos x ->
      X_Neg x
    | X_Neg x ->
      X_Pos x

  let blast_atom r = function
    | t, Some op ->
      X_True
    | t, None ->
      X_True

  let rec blast_formula r = function
    | Formula.F_True ->
      X_True
    | Formula.F_Not g ->
      xnot (blast_formula r g)
    | _ ->
      X_True

  let assert_formula {r_q} =
    Dequeue.push_back r_q

  let solve ({r_q} as r) =
    Dequeue.iter r_q ~f:(Fn.compose ignore (blast_formula r));
    Dequeue.clear r_q;
    R_Sat

end
