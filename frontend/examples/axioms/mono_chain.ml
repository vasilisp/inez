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

(* n variables *)

let vars =
  let f _ = fresh_int_var () in
  Array.init n ~f ;;

(* constraints *)

for i = 0 to n - 3 do
  let i_plus_1 = i + 1 in
  constrain (~logic (f vars.(i) <= f vars.(i_plus_1)))
done ;;

constrain
  (let n_minus_1 = n - 1 and n_minus_2 = n - 2 in
   if unsat then
     ~logic (f vars.(n_minus_2) < f vars.(n_minus_1))
   else
     ~logic (f vars.(n_minus_2) <= f vars.(n_minus_1))) ;;

constrain
  (let zero = 0 and n_minus_1 = n - 1 in
   ~logic (vars.(zero) > vars.(n_minus_1))) ;;

solve_print_result () ;;
