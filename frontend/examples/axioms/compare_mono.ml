open Core.Std
open Script

let sat = Array.length argv >= 2 && argv.(1) = "--sat" ;;

(* OCaml-style, int-valued 'compare' function *)

let compare a b = ~free ;;

assert_axiom (~forall a ([], compare a a = 0)) ;;

assert_axiom (~forall a (~forall b ([a < b], compare a b < 0))) ;;

assert_axiom (~forall a (~forall b ([a > b], compare a b > 0))) ;;

(* monotonically increasing function 'f' *)

let f _ = ~free ;;

assert_axiom (~forall x (~forall y ([x < y], f x < f y))) ;;

(* problem variables *)

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

if not sat then constrain (~logic (not (a = b))) ;;

constrain (~logic (compare (f a) (f b) = 0)) ;;

solve_print_result () ;;

ideref_printf "a: %d\n%!" a ;;

ideref_printf "b: %d\n%!" b ;;
