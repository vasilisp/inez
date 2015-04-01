open Script ;;

open Core.Std ;;

(* vars *)

let x = fresh_int_var () ;;

let y = fresh_int_var () ;;

let z = fresh_int_var () ;;

(* UF *)

let f _ = ~free ;;

(*
assert_axiom
  (~forall x (~forall y ([x < y], f x <= f y))) ;;
*)

assert_axiom
  (~forall x (~forall y ([f x < f y], x < y))) ;;

(* objective *)

minimize (~logic (- y)) ;;

(* constraints *)

constrain (~logic (2 * y - x <= 3)) ;;

constrain (~logic (3 * x + y <= 12)) ;;

constrain (~logic (f x > f y)) ;;

constrain (~logic (x >= 0)) ;;

constrain (~logic (y >= 0)) ;;

(* solve and print *)

solve_print_result () ;;

ideref_printf "x -> %d\n" x ;;

ideref_printf "y -> %d\n" y ;;
