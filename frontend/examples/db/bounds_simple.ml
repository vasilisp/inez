open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|13633; 23193; 1230; 6800; 30314|] ;;

let random_int = Random.State.int state ;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    1000 ;;

let synthesize =
  Array.length argv >= 3 && argv.(2) = "--synthesize" ;;

type ii = (Int, Int) Schema ;;
  
let db =
  let f i = make_row_ii (~logic (toi i, 10 * toi i)) in
  let l = List.init n ~f in
  let l =
    if synthesize then
      let v = fresh_int_var () in
      let k = toi (10 * n) in
      constrain (~logic (v < k));
      make_row_ii (~logic (toi n, v)) :: l
    else
      l in
  make_db_ii l ;;

constrain
  (let k = toi (10 * n) in
   ~logic (exists (sel db (fun (_, v : Row) -> v >= k)))) ;;

solve_print_result () ;;
