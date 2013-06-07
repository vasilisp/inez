open Db_logic

let ideref_human x =
  Option.(ideref x >>= Int63.to_int) ;;

let make_entry (a, b) =
  R.R_Pair (R.R_Int a, R.R_Int b) ;;

let make_db l =
  D.D_Input
    (S.S_Pair (S.S_Int, S.S_Int),
     List.map l ~f:make_entry) ;;

let u = fresh_int_var () ;;

let v = fresh_int_var () ;;

let db1 = make_db
  [toi 12, toi 12;
   toi 23, u] ;;

let db2 = make_db
  [toi 30, toi 23;
   toi 40, toi 0] ;;

let db_cross = cross db1 db2 ;;

constrain
  (exists
     (sel db_cross
        (fun (R.R_Pair (R.R_Pair (_, R.R_Int x), R.R_Pair (R.R_Int y, _))) ->
          logic in x = y + 1))) ;;

(* constrain (Ops.(u = toi 32)) ;; *)

solve () ;;

ideref_human v ;;

ideref_human u ;;
