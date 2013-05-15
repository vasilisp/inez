open Core.Std
open Terminology

module I = Lang_ids.Make (struct end)

module O = Smtlib_solver.Make(Solver.Make(Scip.Scip_basic)(I))(I)

let _ =
  let f = function
    | Smtlib_solver.R.P_Unsupported ->
      Printf.printf "unsupported\n%!"
    | Smtlib_solver.R.P_Syntax ->
      Printf.printf "syntax error\n%!"
    | Smtlib_solver.R.P_Type ->
      Printf.printf "type error\n%!"
    | Smtlib_solver.R.P_Ok Some (R_Opt | R_Unbounded | R_Sat) ->
      Printf.printf "sat\n%!";
    | Smtlib_solver.R.P_Ok Some R_Unsat ->
      Printf.printf "unsat\n%!";
    | Smtlib_solver.R.P_Ok Some R_Unknown ->
      Printf.printf "unknown\n%!"
    | Smtlib_solver.R.P_Ok None ->
      ()
  and f_err () = Printf.printf "error\n%!" in
  (* and channel = open_in Sys.argv.(1) in *)
  O.main stdin ~f ~f_err
