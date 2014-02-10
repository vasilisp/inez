open Core.Std ;;
open Db_script ;;

let state = Random.State.make [|215143; 6764; 936217; 435|] ;;

let random_int = Random.State.int state ;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    100 ;;

let double =
  Array.length argv >= 3 && String.equal argv.(2) "--double" ;;

type ii = (
  Int,
  Int
) Schema ;;

let db =
  let f i =
    let j = if double then 2 * i else i + 1 in
    make_row_ii (toi i, toi j) in
  make_db_ii
    (match List.init n ~f with
    | _ :: d when double ->
      d
    | l ->
      l) ;;

(* there exists an employee whose salary + bonus exceeds the limit *)

constrain
  (let f (x, y : Row) =
     ~logic (x = y) in
   ~logic (exists (sel db f))) ;;

solve_print_result () ;;
