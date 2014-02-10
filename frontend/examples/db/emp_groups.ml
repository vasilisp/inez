open Core.Std ;;
open Db_script ;;

let state = Random.State.make [|215143; 6764; 936217; 435|] ;;

let random_int = Random.State.int state ;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    100 ;;

type salary = (
  Int,  (* employee ID *)
  Int   (* salary *)
) Schema ;;

type bonus = (
  Int,  (* employee ID *)
  Int   (* bonus *)
) Schema ;;

type group = (
  Int,  (* group upper bound *)
  Int   (* group lower bound *)
) Schema ;;

let income_lb = 40_000  (* inclusive *) ;;

let income_ub = 300_001 (* exclusive *) ;;

let groups =
  let groups =
    ~logic [toi income_lb, 60_000;
            60_000, 100_000;
            100_000, 140_000;
            140_000, 200_000;
            200_000, toi income_ub]
  and f = make_row_group in
  make_db_group (List.map groups ~f) ;;
let in_group lb ub s b =
  ~logic (lb <= s + b && s + b < ub) ;;

let l_salaries, l_bonuses =
  let f i =
    let salary = income_lb + random_int (income_ub - income_lb) in
    let diff = income_ub - salary in
    let bonus = random_int diff in
    assert (salary + bonus < income_ub);
    make_row_salary (toi i, toi salary),
    make_row_bonus (toi i, toi bonus) in
  List.unzip (List.init n ~f)

(* possibly adding synthetic tuples *)

let l_salaries, l_bonuses =
  let f i =
    let s = fresh_int_var ()
    and b = fresh_int_var () in
    constrain (~logic (s >= 0));
    constrain (~logic (b >= 0));
    make_row_salary (toi (n + i), s),
    make_row_bonus (toi (n + i), b) in
  let l_salaries', l_bonuses' = List.unzip (List.init 6 ~f) in
  l_salaries' @ l_salaries, l_bonuses' @ l_bonuses ;;

let salaries = make_db_salary l_salaries ;;

let bonuses = make_db_bonus l_bonuses ;;

let salaries_bonuses =
  let f (i, _, i', _ : Row) = ~logic (i = i') in
  ~logic (sel (cross salaries bonuses) f) ;;

(*

  For testing an app, we want to make sure that the (synthesized +
  concrete data is somewhat diverse: all groups are inhabited, and
  there is even an employee outside the groups.

*)

(* every group is inhabited *)

constrain
  (let f (lb, ub : Row) =
     let f (_, s, _, b : Row) =
       ~logic (in_group lb ub s b) in
     ~logic (not (exists (sel salaries_bonuses f))) in
   ~logic (not (exists (sel groups f)))) ;;

(* there exists an employee whose salary + bonus does not fit in any
   of the groups *)

constrain
  (let f (_, s, _, b : Row) =
     let f (lb, ub : Row) = ~logic (in_group lb ub s b) in
     ~logic (not (exists (sel groups f))) in
   ~logic (exists (sel salaries_bonuses f))) ;;

solve_print_result () ;;
