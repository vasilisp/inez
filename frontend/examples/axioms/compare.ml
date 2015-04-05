open Core.Std
open Script

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let sat = Array.length argv >= 3 && argv.(2) = "--sat" ;;

assert (n >= 0) ;;

assert (n > 1 || not sat) ;;

let compare a b = ~free ;;

(* OCaml-style, int-valued compare function *)

assert_axiom (~forall a ([], compare a a = 0)) ;;

assert_axiom (~forall a (~forall b ([a < b], compare a b < 0))) ;;

assert_axiom (~forall a (~forall b ([a > b], compare a b > 0))) ;;

let f _ = ~free ;;

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

for i = 0 to n - 1 do
  if i = n / 2 && sat then
    let i = toi i in
    constrain (~logic (f (i - 1) <= f i))
  else
    let i = toi i in
    constrain (~logic (f (i - 1) < f i))
done ;;

constrain (~logic (0 <= a && a < toi n)) ;;

constrain (~logic (0 <= b && b < toi n)) ;;

constrain (~logic (not (a = b))) ;;

constrain (~logic (compare (f a) (f b) = 0)) ;;

solve_print_result () ;;

ideref_printf "a: %d\n%!" a ;;

ideref_printf "b: %d\n%!" b ;;
