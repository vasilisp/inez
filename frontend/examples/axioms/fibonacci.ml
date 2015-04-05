open Core.Std ;;
open Script ;;

let n = 10 ;;

assert (n > 0) ;;

let f _ = ~free ;;

assert_axiom
  (~forall n ([n >= 2], (f n = f (n - 1) + f (n - 2)))) ;;

constrain (~logic (f 0 = 0)) ;;

constrain (~logic (f 1 = 1)) ;;

let a = fresh_int_var () ;;

constrain (~logic (a > 0)) ;;

constrain (~logic (a < toi n)) ;;

constrain (~logic (a >= f a)) ;;

(*

  Our axiomatization of fibonacci is not a local theory. Make sure
  that there are enough terms in the input to pull in the required
  axiom instances.

*)

for i = 0 to n - 1 do
  constrain (~logic (fresh_int_var () = f (toi i)))
done ;;

minimize (~logic (- a)) ;;

solve_print_result () ;;

ideref_printf "a -> %d\n" a ;;
