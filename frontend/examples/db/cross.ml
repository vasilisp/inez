open Core.Std ;;
open Script_db_solver ;;

let n =
  if Array.length Sys.argv >= 3 then
    int_of_string Sys.argv.(2)
  else
    10000 ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    ()

type iib = (Int, Int, Bool) Schema ;;

let db11 = fresh_int_var () ;;

let db12 = fresh_int_var () ;;

let db21 = fresh_int_var () ;;

let db22 = fresh_int_var () ;;

let db1 =
  make_db_iib
    (make_row_iib (db11, db12, ~logic true) ::
       (let f i = ~logic (make_row_iib (toi i, 2 * toi i, true)) in
        List.init n ~f)) ;;

let db2 =
  make_db_iib
    (make_row_iib (db21, db22, ~logic true) ::
       (let f i = ~logic (make_row_iib (toi i, 2 * toi i, false)) in
        List.init n ~f)) ;;

let db_cross = ~logic (cross db1 db2) ;;

let db_cross_cross = ~logic (cross db_cross db_cross) ;;

constrain
  (~logic
      (let f (x, _, _, x', y , _,
              _, z, _, _ , z', (w : Bool) : Row) =
         x + y = 18000 &&
         x >= 45000 &&
         not (x = x') &&
         z = z' && w in
       exists (sel db_cross_cross f))) ;;

print_endline (string_of_result (solve ())) ;;

ideref_print "db11" db11 ;;

ideref_print "db12" db12 ;;

ideref_print "db21" db21 ;;

ideref_print "db22" db22 ;;
