open Db_logic

let ideref_human x =
  Option.(ideref x >>= Int63.to_int) ;;

type entry = (Int, Int) Schema ;;

let make_db l =
  make_db_entry (List.map l ~f:(Tuple2.uncurry make_row_entry)) ;;

let v = fresh_int_var () ;;

let u = fresh_int_var () ;;

let db =
  make_db
    (~logic
        [12, 12;
         23, v;
         32, u]) ;;

constrain
  (exists
     (sel db
        (function (_, x : Row) -> ~logic (x = 1821)))) ;;

constrain (~logic (v = 18)) ;;

solve () ;;

ideref_human v ;;

ideref_human u ;;

