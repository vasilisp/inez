open Core.Std
open Script

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let unsat = Array.length argv >= 3 && argv.(2) = "--unsat" ;;

assert (n >= 1) ;;

let compare a b = ~free ;;

(* OCaml-style, int-valued compare function *)

assert_axiom (~forall a ([], compare a a = 0)) ;;

assert_axiom (~forall a (~forall b ([a < b], compare a b < 0))) ;;

assert_axiom (~forall a (~forall b ([a > b], compare a b > 0))) ;;

(* n variables *)

let vars =
  let f _ = fresh_int_var () in
  Array.init n ~f ;;

for i = 0 to n - 2 do
  constrain
    ((~logic (if unsat then (<) else (<=)))
        vars.(i)
        vars.(i + 1))
done ;;

constrain
  ((~logic (if unsat then (<) else (<=)))
      vars.(n - 1)
      vars.(0)) ;;

let result = solve () ;;

string_of_result result |> Printf.printf "%s\n%!" ;;

match result with
| Terminology.R_Opt
| Terminology.R_Unbounded
| Terminology.R_Sat ->
  for i = 0 to n - 2 do
    Printf.printf "v%d = " i;
    ideref_printf "%d\n%!" vars.(i)
  done
| _ ->
  () ;;
