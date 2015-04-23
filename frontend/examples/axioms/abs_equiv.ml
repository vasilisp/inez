open Core.Std ;;
open Script ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

(* axiomatized uninterpreted abs *)

let abs _ = ~free ;;

assert_axiom
  (~forall x ([x < 0], abs x = - x)) ;;

assert_axiom
  (~forall x ([x >= 0], abs x = x)) ;;

(* abs 'macro' *)

let abs' v = ~logic (iite (v >= 0) v (- v)) ;;

let v = fresh_int_var () ;;

(* takes too long without bounds *)

constrain (~logic (-5000 <= v && v <= 5000)) ;;

constrain (~logic (not (abs v = abs' v)));;

solve_print_result () ;;
