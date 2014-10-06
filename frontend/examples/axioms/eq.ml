open Core.Std
open Script

let compare a b = ~free ;;

(* OCaml-style, int-valued compare function *)

assert_axiom (~forall a ([], compare a a = 0)) ;;

assert_axiom (~forall a (~forall b ([a < b], compare a b < 0))) ;;

assert_axiom (~forall a (~forall b ([a > b], compare a b > 0))) ;;

let f _ = ~free ;;

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

constrain (~logic (compare a b = compare b a)) ;;

constrain (~logic (not (f a = f b))) ;;

solve_print_result () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

ideref_print "a" a ;;

ideref_print "b" b ;;
