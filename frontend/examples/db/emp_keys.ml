open Core.Std ;;
open Db_script ;;

let state = Random.State.make [|2633; 23386; 7227; 28274; 8470|] ;;

let random_int = Random.State.int state ;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    100 ;;

type employee = (
  Int,  (* ID *)
  Int   (* age *)
) Schema ;;

type income = (
  Int,  (* employee ID *)
  Int   (* salary amount *)
) Schema ;;

let employees =
  make_db_employee
    (List.init n
       ~f:(fun i ->
         let age = 18 + random_int (65 - 18) in
         make_row_employee (toi i, toi age))) ;;

let mk_unequal_variables m =
  let rec f acc = function
    | a :: ((ad :: _) as d) ->
      f (~logic (a < ad && acc)) d
    | _ ->
      acc in
  let l = let f _ = fresh_int_var () in List.init m ~f in
  constrain (~logic (f true l)); l

let income =
  let f v =
    let salary = 50_000 + random_int 100_000 in
    make_row_income (v, toi salary) in
  make_db_income (List.map (mk_unequal_variables n) ~f) ;;

(* foreign key on income *)

constrain
  (let f (id, _ : Row) =
     let f (id', _ : Row) = ~logic (id = id') in
     ~logic (not (exists (sel employees f))) in
   ~logic (not (exists (sel income f)))) ;;

solve_print_result () ;;
