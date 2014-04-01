module S = Db_solver.Make(Scip.Scip_with_dp)(Id_for_scripts)

let ctx = S.make_ctx `Lazy

type c = Id_for_scripts.c

let constrain g =
  match S.assert_formula ctx g with
  | `Ok ->
    ()
  | `Out_of_fragment ->
    raise (Invalid_argument "constrain: formula out of fragment")

let minimize m =
  match S.add_objective ctx m with
  | `Ok ->
    ()
  | `Duplicate ->
    raise (Invalid_argument "problem has objective already")
  | `Out_of_fragment ->
    raise (Invalid_argument "minimize: term out of fragment")

let solve () =
  S.solve ctx

let fresh_int_var () =
  Db_logic.M.M_Var (Id_for_scripts.gen_id Type.Y_Int)

let fresh_bool_var () =
  Formula.F_Atom
    (Db_logic.A.A_Bool
       (Db_logic.M.M_Var (Id_for_scripts.gen_id Type.Y_Bool)))

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

let solve_print_result () =
  print_endline (string_of_result (solve ()))

let argv =
  if !Sys.interactive then
    Sys.argv
  else
    let open Core.Std.Array in
    slice Sys.argv 1 (length Sys.argv)
