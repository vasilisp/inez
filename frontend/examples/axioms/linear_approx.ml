open Core.Std
open Script

let u = 3 ;;

let x_0  = toi 27 ;;

(* function 'f' linear approximation around x_0 *)

let f _ = ~free ;;

assert_axiom (~forall x ([x <= x_0], f x <= f x_0)) ;;

assert_axiom (~forall x ([x_0 <= x], f x_0 <= f x)) ;;

assert_axiom
  (let u = Int63.of_int u in
   ~forall x ([x <= x_0], f x_0 - f x <= u * (x_0 - x))) ;;

assert_axiom
  (let u = Int63.of_int u in
   ~forall x ([x >= x_0], f x - f x_0 <= u * (x - x_0))) ;;

(* problem variables *)

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

constrain (~logic (a > b && b > x_0)) ;;

constrain (~logic (f a - f b > Int63.of_int u * (a - x_0))) ;;

solve_print_result () ;;

ideref_printf "a: %d\n%!" a ;;

ideref_printf "b: %d\n%!" b ;;
