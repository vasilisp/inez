open Core.Std ;;
open Script ;;

let (|?) _ _ = ~free ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let even x =
  let x_2 = fresh_int_var () in
  ~logic (2 * x_2 = x) ;;

let odd x =
  let x_2 = fresh_int_var () in
  ~logic (2 * x_2 + 1 = x) ;;

(* forall x y . x |? y = x \/ x |? y = y *)

assert_axiom
  (~forall x (~forall y ([x |? y < x], x |? y = y))) ;;

assert_axiom
  (~forall x (~forall y ([x |? y > x], x |? y = y))) ;;

(* f n x = x |? x + 1 |? ... |? x + n - 1 *)

let x = fresh_int_var () ;;

constrain (even x) ;;

let y = fresh_int_var () ;;

constrain (even y) ;;

let c = fresh_int_var () ;;

constrain (~logic (c = (x |? y))) ;;

constrain (odd (x |? y)) ;;

solve_print_result () ;;

ideref_printf "x -> %d\n" x ;;

ideref_printf "y -> %d\n" y ;;

ideref_printf "c -> %d\n" c ;;
