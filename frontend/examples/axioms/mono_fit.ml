open Core.Std ;;
open Script ;;

(* input *)

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let unsat = Array.length argv >= 3 && argv.(2) = "--unsat" ;;

assert (n >= 0) ;;

(* monotonically increasing function f *)

let f _ = ~free ;;

assert_axiom
  (~forall a (~forall b ([a <= b], f a <= f b))) ;;

(* n variables *)

let vars =
  let f _ =
    let v = fresh_int_var () in
    constrain (~logic (v >= 0));
    constrain (~logic (v <= toi n - if unsat then 2 else 1));
    v in
  List.init n ~f ;;

(* constraints *)

let iter_pairs l ~f =
  let rec iter_pairs_aux = function
    | a :: d ->
      List.iter d ~f:(f a); iter_pairs_aux d
    | [] ->
      () in
  iter_pairs_aux l ;;

let _ =
  let f v1 v2 = constrain (~logic (not (f v1 = f v2))) in
  iter_pairs vars ~f ;;

solve_print_result () ;;
