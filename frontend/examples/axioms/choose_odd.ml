open Core.Std ;;
open Lt_script ;;

let (|?) _ _ = ~free ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let even x =
  let x_2 = fresh_int_var () in
  ~logic (2 * x_2 = x) ;;

let odd x =
  let x_2 = fresh_int_var () in
  ~logic (2 * x_2 + 1 = x) ;;

(* forall x y . x |? y = x \/ x |? y = y *)

assert_axiom
  (~forall x (~forall y ([x |? y < x], x |? y = y))) ;;

assert_axiom
  (~forall x (~forall y ([x |? y > x], x |? y = y))) ;;

(* f n x = x |? x + 1 |? ... |? x + n - 1 *)

let f n x =
  let rec f k ~acc =
    if k >= n then
      acc
    else
      let two_k = 2 * k in
      let acc = ~logic ((x + toi two_k) |? acc) in
      f (k + 1) ~acc 
  and acc = x in
  f 1 ~acc ;;

let x = fresh_int_var () ;;

constrain (even x) ;;

let c = f n x ;;

constrain (~logic (odd c)) ;;

solve_print_result () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

ideref_print "x" x ;;
