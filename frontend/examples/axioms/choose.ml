open Core.Std ;;
open Script ;;

let (|/) _ _ = ~free ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let unsat = Array.length argv >= 3 && argv.(2) = "--unsat" ;;

(* forall x y . x |/ y = x \/ x |/ y = y *)

assert_axiom
  (~forall x (~forall y ([x |/ y < x], x |/ y = y))) ;;

assert_axiom
  (~forall x (~forall y ([x |/ y > x], x |/ y = y))) ;;

(* f n x = x |/ x + 1 |/ ... |/ x + n - 1 *)

let f n x =
  let rec f k ~acc =
    if k >= n then
      acc
    else
      let acc = ~logic ((x + toi k) |/ acc) in
      f (k + 1) ~acc 
  and acc = x in
  f 1 ~acc ;;

let x = fresh_int_var () ;;

let c = f n x ;;

constrain
  (if unsat then
      ~logic (c >= x + toi n)
   else
      ~logic (c >= x + toi n - 1)) ;;

solve_print_result () ;;

ideref_printf "x -> %d\n" x ;;
