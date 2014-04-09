open Core.Std ;;
open Lt_script ;;

let choose _ _ = ~free ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

(* forall x y . choose x y = x \/ choose x y = y *)

assert_axiom
  (~forall x (~forall y ([choose x y < x], choose x y <= y))) ;;

assert_axiom
  (~forall x (~forall y ([choose x y < x], choose x y >= y))) ;;

assert_axiom
  (~forall x (~forall y ([choose x y > x], choose x y <= y))) ;;

assert_axiom
  (~forall x (~forall y ([choose x y > x], choose x y >= y))) ;;

let f n x =
  let rec f k ~acc =
    if k >= n then
      acc
    else
      let acc = ~logic (choose (x + toi k) acc) in
      f (k + 1) ~acc 
  and acc = x in
  f 1 ~acc ;;

let x = fresh_int_var () ;;

let c = f n x ;;

constrain (~logic (c >= x + toi n)) ;;

solve_print_result () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

ideref_print "x" x ;;
