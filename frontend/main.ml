open Core.Std
open Terminology

module I = Lang_ids.Make (struct end)

module O = Smtlib_solver.Make(Solver.Make(Scip)(I))(I)

let _ =
  let f = function
    | Smtlib_solver.R.P_Unsupported ->
      print_string "unsupported\n"
    | Smtlib_solver.R.P_Syntax ->
      print_string "syntax error\n"
    | Smtlib_solver.R.P_Type ->
      print_string "type error\n"
    | Smtlib_solver.R.P_Ok Some (R_Opt | R_Unbounded | R_Sat) ->
      print_string "sat\n";
    | Smtlib_solver.R.P_Ok Some R_Unsat ->
      print_string "unsat\n";
    | Smtlib_solver.R.P_Ok Some R_Unknown ->
      print_string "unknown\n"
    | Smtlib_solver.R.P_Ok None ->
      ()
  and f_err () = print_string "error\n" in
  (* and channel = open_in Sys.argv.(1) in *)
  O.main stdin ~f ~f_err
