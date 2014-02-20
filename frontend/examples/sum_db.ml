open Db_script ;;
open Core.Std ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    20 ;;

type sum = (
  Int,
  Int,
  Int
) Schema ;;

let (+!) x y = ~free ;;

let db_sum =
  make_db_sum
    (List.join
       (List.init n
          ~f:(fun i ->
            List.init n
              ~f:(fun j ->
                let i = toi i
                and j = toi j
                and s = toi ((i + j) % n) in
                constrain (~logic (i +! j = s));
                make_row_sum (i, j, i +! j))))) ;;

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

constrain
  (~logic (exists
             (let f (a', b', s : Row) =
                ~logic (a = a' && b = b' && a +! b = s) in
              sel db_sum f))) ;;

constrain (~logic (a +! b >= toi n)) ;;

solve_print_result () ;;
