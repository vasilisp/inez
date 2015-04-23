open Core.Std ;;
open Script ;;

(* input *)

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let unsat = Array.length argv >= 3 && argv.(2) = "--unsat" ;;

assert (n >= 0) ;;

(* bounds *)

let l = fresh_int_var () ;;

let u = fresh_int_var () ;;

let l' = fresh_int_var () ;;

let u' = fresh_int_var () ;;

(* problem variables *)

let v = fresh_int_var () ;;

let w = fresh_int_var () ;;

(* bounded function f : for x in [l, u], l' <= f(x) <= u' *)

let f _ = ~free ;;

assert_axiom (~forall x ([l <= x; x <= u], l' <= f x)) ;;

assert_axiom (~forall x ([l <= x; x <= u], f x <= u')) ;;

(* function g *)

let g _ = ~free ;;

(* constraints *)

for i = 0 to n - 1 do
  let i = toi i in
  constrain (~logic (l <= g i && g i <= u))
done ;;

constrain (~logic (0 <= v && v < toi n)) ;;

constrain (~logic (0 <= w && w < toi n)) ;;

constrain
  (if unsat then
      ~logic (f (g v) - f (g w) > u' - l')
   else
      ~logic (f (g v) - f (g w) >= u' - l')) ;;

solve_print_result () ;;
