open Core.Std ;;
open Lt_script ;;

let car _ = ~free ;;

let cdr _ = ~free ;;

let cons _ _ = ~free ;;

assert_axiom
  (~forall x (~forall y ([], car (cons x y) <= x))) ;;

assert_axiom
  (~forall x (~forall y ([], x <= car (cons x y)))) ;;

assert_axiom
  (~forall x (~forall y ([], cdr (cons x y) <= y))) ;;

assert_axiom
  (~forall x (~forall y ([], y <= cdr (cons x y)))) ;;

let x = fresh_int_var () ;;

let y = fresh_int_var () ;;

let z = fresh_int_var () ;;

constrain (~logic (cdr (cons x y) >= 3)) ;;

constrain (~logic (car (cons y z) <= 2)) ;;

solve_print_result () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

ideref_print "x" x ;;

ideref_print "y" y ;;

ideref_print "z" z ;;
