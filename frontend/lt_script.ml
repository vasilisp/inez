module S = Axiom_solver.Make(Scip.Scip_with_cut_gen)(Id_for_scripts)

type c = Id_for_scripts.c

let ctx = S.make_ctx ()

let constrain =
  S.assert_formula ctx

let solve () =
  S.solve ctx

let fresh_int_var () =
  Logic.M.M_Var (Id_for_scripts.gen_id Type.Y_Int)

let fresh_bool_var () =
  Formula.F_Atom
    (Logic.A.A_Bool
       (Logic.M.M_Var (Id_for_scripts.gen_id Type.Y_Bool)))

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

let minimize o =
  match S.add_objective ctx o with
  | `Ok ->
    ()
  | `Duplicate ->
    raise (Invalid_argument "problem has objective already")

let solve_print_result () =
  print_endline (string_of_result (solve ()))

let assert_axiom = S.assert_axiom ctx

let argv =
  if !Sys.interactive then
    Sys.argv
  else
    let open Core.Std.Array in
    slice Sys.argv 1 (length Sys.argv)
