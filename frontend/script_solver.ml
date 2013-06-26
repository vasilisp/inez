module Id' = Id.Make (struct end)
module S = Solver.Make(Scip.Scip_basic)(Id')

let ctx = S.make_ctx (Scip.Scip_basic.make_ctx ())

type c = Id'.c

let constrain =
  S.assert_formula ctx

let solve () =
  S.solve ctx

let fresh_int_var () =
  Logic.M.M_Var (Id'.gen_id Type.Y_Int)

let fresh_bool_var () =
  Formula.F_Atom
    (Logic.A.A_Bool
       (Logic.M.M_Var (Id'.gen_id Type.Y_Bool)))

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

let gen_id = Id'.gen_id

let string_of_result =
  let open Terminology in
  function
  | R_Opt ->
    "opt"
  | R_Sat ->
    "sat"
  | R_Unbounded ->
    "unbounded"
  | R_Unsat ->
    "unsat"
  | R_Unknown ->
    "unknown"
