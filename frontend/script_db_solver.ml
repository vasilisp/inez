module Id' = Id.Make (struct end)

module S = Db_solver.Make(Scip.Scip_with_dp)(Id')
let ctx = S.make_ctx ()

type c = Id'.c

let constrain g =
  match S.assert_formula ctx g with
  | `Ok ->
    ()
  | `Fail ->
    raise (Invalid_argument "constrain: non-existential formula")

let solve () =
  S.solve ctx

let fresh_int_var () =
  Db_logic.M.M_Var (Id'.gen_id Type.Y_Int)

let fresh_bool_var () =
  Formula.F_Atom
    (Db_logic.A.A_Bool
       (Db_logic.M.M_Var (Id'.gen_id Type.Y_Bool)))

let ideref = function
  | Db_logic.M.M_Var v ->
    S.deref_int ctx v
  | _ ->
    None

let bderef = function
  | Formula.F_Atom (Db_logic.A.A_Bool (Db_logic.M.M_Var v)) ->
    S.deref_bool ctx v
  | _ ->
    None

let toi x =
  Db_logic.M.M_Int (Core.Std.Int63.of_int x)

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
