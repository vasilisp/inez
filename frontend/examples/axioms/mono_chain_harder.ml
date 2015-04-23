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

(* monotonically increasing function f *)

let f _ = ~free ;;

assert_axiom
  (~forall a (~forall b ([a <= b], f a <= f b))) ;;

(* function g *)

let g _ = ~free ;;

(* variables *)

let v = fresh_int_var () ;;

let w = fresh_int_var () ;;

(* constraints *)

constrain
  (~logic (0 <= v && v <= toi n - 1)) ;;

constrain
  (~logic (v < w && w <= toi n - if unsat then 1 else 0)) ;;

for i = 0 to n - 2 do
  let i = toi i in
  constrain (~logic (f (g i) < f (g (i + 1))))
done ;;

constrain (~logic (g v > g w)) ;;

solve_print_result () ;;
