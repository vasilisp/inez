open Script ;;

open Core.Std ;;

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

ideref_printf "x: %i\n" x ;;

ideref_printf "y: %i\n" y ;;
