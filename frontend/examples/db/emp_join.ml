open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|15038; 19624; 31779; 2891; 13009|] ;;

let random_int = Random.State.int state ;;

(* parameters from the command line *)

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    100 ;;

assert (n >= 4) ;;

let synthesize =
  Array.length argv >= 3 && argv.(2) = "--synthesize" ;;

let synthesize_unsat =
  Array.length argv >= 4 && argv.(3) = "--synthesize-unsat" ;;

(* database schema *)

type employee = (
  Int,  (* employee ID *)
  Int,  (* age *)
  Int   (* level: 0 = junior, 1 = middle, 2 = senior *)
) Schema ;;

type bonus = (
  Int,  (* employee ID *)
  Int   (* amount *)
) Schema ;;

let base_salary = 30_000 ;;

(* Total income is calculated as follows: *)

let base_income age level =
  base_salary + 20_000 * level + 500 * (age - 18) ;;

let base_income_symbolic age level =
  ~logic (toi base_salary + 20_000 * level + 500 * (age - 18)) ;;

(* total_income = base_income + bonus *)

(*

  We produce [n] constant tuples employees. The data satisfies the
  following constraints:

  - ID >= 0
  
  - ID is unique

  - age >= 18

  - level >= 2 -> age >= 30

  We also produce constant tuples for bonuses that satisfy the
  following constraints:

  - foreign key on employee ID

  - employee ID is unique (i.e., at most one tuple per employee)

  - 0 <= bonus <= base_income * (1 / 4)
  
*)

let l_employees, l_bonuses =
  let f i =
    if i < n * 3 / 4 then
      let age = 30 + random_int 36
      and level = random_int 3 in
      let base = base_income age level in
      let bonus = max (random_int (base / 4 + 1)) 1 in
      make_row_employee (toi i, toi age, toi level),
      Some (make_row_bonus (toi i, toi bonus))
    else
      let age = 18 + random_int 12
      and level = random_int 2 in
      make_row_employee (toi i, toi age, toi level),
      None in
  List.unzip (List.init n ~f) ;;

let l_bonuses = List.filter_opt l_bonuses ;;

let employees = make_db_employee l_employees ;;

(* possibly adding synthetic tuples *)

let l_bonuses =
  if synthesize || synthesize_unsat then
    let id = fresh_int_var ()
    and amount = fresh_int_var () in
    constrain (~logic (amount >= 0));
    constrain (~logic (id >= 0));
    (let f (id', age, level : Row) =
       ~logic (id = id' &&
           4 * amount <= base_income_symbolic age level) in
     constrain (~logic (exists (sel employees f))));
    make_row_bonus (id, amount) :: l_bonuses
  else
    l_bonuses ;;

let bonuses = make_db_bonus l_bonuses ;;

let eb =
  let f (id, _, _, id', _ : Row) = ~logic (id = id') in
  ~logic (sel (cross employees bonuses) f) ;;

(* there exists an employee younger than 30 whose total income exceeds
   70_000 *)

constrain
  (let limit = toi (if synthesize_unsat then 70_000 else 69_000) in
   let f (_, age, level, _, amount : Row) =
     ~logic (age < 30 && 
               base_income_symbolic age level + amount >= limit) in
   ~logic (exists (sel eb f))) ;;

solve_print_result () ;;
