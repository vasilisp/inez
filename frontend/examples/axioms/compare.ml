open Core.Std
open Script

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let compare a b = ~free ;;

(* OCaml-style, int-valued compare function *)

assert_axiom (~forall a ([], compare a a = 0)) ;;

assert_axiom (~forall a (~forall b ([a < b], compare a b < 0))) ;;

assert_axiom (~forall a (~forall b ([a > b], compare a b > 0))) ;;

let f _ = ~free ;;

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

let mk_unequal_variables n =
  let rec f acc = function
    | a :: ((ad :: _) as d) ->
      f (~logic (a < ad && acc)) d
    | _ ->
      acc in
  let l = let f _ = fresh_int_var () in List.init n ~f in
  constrain (~logic (f true l)); l ;;

let l = mk_unequal_variables n ;;

let _ =
  List.iteri l ~f:(fun i x -> constrain (~logic (f (toi i) = x))) ;;

constrain (~logic (0 <= a && a < toi n)) ;;

constrain (~logic (0 <= b && b < toi n)) ;;

constrain (~logic (not (a = b))) ;;

constrain (~logic (compare (f a) (f b) = 0)) ;;

solve_print_result () ;;

ideref_printf "a: %d\n%!" a ;;

ideref_printf "b: %d\n%!" b ;;
