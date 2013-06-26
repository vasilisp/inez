open Script_db_solver ;;
open Core.Std ;;

type entry = (Int, Int) Schema ;;

let make_db l =
  make_db_entry (List.map l ~f:make_row_entry) ;;

let v = fresh_int_var () ;;

let u = fresh_int_var () ;;

let db =
  make_db
    (~logic
        [12, 12;
         23, v;
         32, u]) ;;

constrain
  (~logic
      (exists
         (sel db (function (_, x : Row) -> x = 1821)))) ;;

constrain (~logic (v = 18)) ;;

let _ =
  let r = solve () in
  print_endline (string_of_result r);
  match r with
  | Terminology.R_Unsat | Terminology.R_Unknown ->
    ()
  | _ ->
    Printf.printf "v = %d\nu = %d\n"
      (Int63.to_string_human (Option.value_exn (ideref v)))
      (Int63.to_string_human (Option.value_exn (ideref u)))
