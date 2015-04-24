open Core.Std ;;

open Script ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

assert (n >= 0) ;;

(* functions f and g *)

let f _ = ~free ;;

let g _ = ~free ;;

assert_axiom (~forall a ([], f a < g a)) ;;

let v = fresh_int_var () ;;

for i = 0 to n - 2 do
  let i = (~logic (v + toi i)) in
  constrain (~logic (f i - g i < f (i + 1) - g (i + 1)))
done ;;

solve_print_result () ;;
