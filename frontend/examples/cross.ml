open Db_logic

let ideref x =
  Option.(ideref x >>= Int63.to_int) ;;

let make_entry (a, b) =
  R.R_Pair (R.R_Int a, R.R_Int b) ;;

let make_db l =
  D.D_Input
    (S.S_Pair (S.S_Int, S.S_Int),
     List.map l ~f:make_entry) ;;

let db11 = fresh_int_var () ;;

let db12 = fresh_int_var () ;;

let db21 = fresh_int_var () ;;

let db22 = fresh_int_var () ;;

let db1 =
  make_db
    ((db11, db12) ::
        List.init 100000 ~f:(fun i -> ~logic (toi i, 2 * toi i))) ;;

let db2 =
  make_db
    ((db21, db22) ::
        List.init 100000 ~f:(fun i -> ~logic (toi i, 2 * toi i))) ;;

let db_cross = cross db1 db2 ;;

constrain (~logic (db11 = 0)) ;;

constrain
  (exists
     (sel db_cross
        (fun (x, _, y, _ : Row) ->
          ~logic (x + y = 18000 && x >= 45000 && y >= 0)))) ;;

solve () ;;

ideref db11 ;;

ideref db21 ;;
