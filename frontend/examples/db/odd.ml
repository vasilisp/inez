open Core.Std ;;
open Db_script ;;

let n =
  if Array.length Sys.argv >= 3 then
    int_of_string Sys.argv.(2)
  else
    100 ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

type ii = (Int, Int) Schema ;;

let db1 = fresh_int_var () ;;

constrain (~logic (db1 >= 0)) ;;
constrain (~logic (db1 < 200)) ;;

let db2 = fresh_int_var () ;;

constrain (~logic (db2 >= 0)) ;;
constrain (~logic (db2 < 200)) ;;

let odd v =
  let i = fresh_int_var () in
  ~logic (v = 2 * i + 1) ;;

let db =
  make_db_ii
    (make_row_ii (~logic (2 * db1 + 1, db2)) ::
     let f _ =
       let i = Random.int 200 in
       let i = 2 * i + 1 in
       ~logic (make_row_ii (toi i, 2 * toi i)) in
     List.init n ~f) ;;

let db_cross = ~logic (cross db db) ;;

constrain
  (~logic
      (let f (x, _, x', _ : Row) = odd (x + x') in
       exists (sel db_cross f))) ;;

print_endline (string_of_result (solve ())) ;;

ideref_print "db1" db1 ;;

ideref_print "db2" db2 ;;
