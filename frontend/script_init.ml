module Id = Id.Make (struct end)
module S = Solver.Make(Scip.Scip_basic)(Id)

let ctx = S.make_ctx (Scip.Scip_basic.make_ctx ())

let constrain g =
  S.assert_formula ctx g

let solve () =
  S.solve ctx

let fresh_int_var () =
  Logic.M.M_Var (Id.gen_id Type.Y_Int)

let fresh_bool_var () =
  Formula.F_Atom
    (Logic.A.A_Bool
       (Logic.M.M_Var (Id.gen_id Type.Y_Bool)))

let ideref = function
  | Logic.M.M_Var v ->
    S.deref_int ctx v
  | _ ->
    None

let bderef = function
  | Formula.F_Atom (Logic.A.A_Bool (Logic.M.M_Var v)) ->
    S.deref_bool ctx v
  | _ ->
    None

let toi x =
  Logic.M.M_Int (Core.Std.Int63.of_int x)
