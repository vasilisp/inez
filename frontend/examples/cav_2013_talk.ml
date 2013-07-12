open Script ;;

open Core.Std ;;

(* utils *)

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

(* vars *)

let x = fresh_int_var () ;;

let y = fresh_int_var () ;;

let z = fresh_int_var () ;;

(* UF *)

let f _ = ~free ;;

(* objective *)

minimize (~logic (- y)) ;;

(* constraints *)

constrain (~logic (2 * y - x <= 3)) ;;

constrain (~logic (3 * x + y <= 12)) ;;

constrain (~logic (f x - f y >= 1)) ;;

constrain (~logic (x >= 0)) ;;

constrain (~logic (y >= 0)) ;;

(* solve and print *)

solve () ;;

ideref_print "x" x ;;

ideref_print "y" y ;;
