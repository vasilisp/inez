open Db_logic ;;

let ideref x =
  Option.(ideref x >>= Int63.to_int) ;;

type iib = (Int, Int, Bool) Schema ;;

let db11 = fresh_int_var () ;;

let db12 = fresh_int_var () ;;

let db21 = fresh_int_var () ;;

let db22 = fresh_int_var () ;;

let db1 =
  make_db_iib
    (make_row_iib db11 db12 (~logic true) ::
       (let f i = ~logic (make_row_iib (toi i) (2 * toi i) true) in
        List.init 100000 ~f)) ;;

let db2 =
  make_db_iib
    (make_row_iib db21 db22 (~logic true) ::
       (let f i = ~logic (make_row_iib (toi i) (2 * toi i) false) in
        List.init 100000 ~f)) ;;

let db_cross = cross db1 db2 ;;

let db_cross_cross = cross db_cross db_cross ;;

constrain
  (exists
     (sel db_cross
        (fun (x , _, _,
              x', y, _ : Row) ->
          ~logic (x + y = 18000 && x >= 45000 && not (x = x'))))) ;;

solve () ;;

ideref db11 ;;

ideref db12 ;;

ideref db21 ;;

ideref db22 ;;
