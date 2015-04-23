open Core.Std ;;
open Script ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let abs _ = ~free ;;

assert_axiom
  (~forall x ([x < 0], abs x = - x)) ;;

assert_axiom
  (~forall x ([x >= 0], abs x = x)) ;;

let vars =
  let f _ =
    let v = fresh_int_var () in
    constrain (~logic (0 <= v));
    v in
  List.init n ~f ;;

constrain (~logic (sum vars ~f:abs < 0)) ;;

solve_print_result () ;;
