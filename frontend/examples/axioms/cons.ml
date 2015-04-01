open Core.Std ;;
open Script ;;

let car _ = ~free ;;

let cdr _ = ~free ;;

let cons _ _ = ~free ;;

assert_axiom
  (~forall x (~forall y ([], car (cons x y) = x))) ;;

assert_axiom
  (~forall x (~forall y ([], cdr (cons x y) = y))) ;;

let x = fresh_int_var () ;;

let y = fresh_int_var () ;;

let z = fresh_int_var () ;;

constrain (~logic (cdr (cons x y) >= 3)) ;;

constrain (~logic (car (cons y z) <= 2)) ;;

solve_print_result () ;;

ideref_printf "x -> %d\n" x ;;

ideref_printf "y -> %d\n" y ;;

ideref_printf "z -> %d\n" z ;;
