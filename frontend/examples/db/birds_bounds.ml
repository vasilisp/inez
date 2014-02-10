open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|15038; 19624; 31779; 2891; 13009|] ;;

let random_int = Random.State.int state ;;

(* input *)

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    1000 ;;

assert (n >= 0 && n % 100 = 0) ;;

let n_individuals =
  if Array.length argv >= 3 then
    int_of_string argv.(2)
  else
    100 ;;

assert (n_individuals >= 10) ;;

let n_species =
  if Array.length argv >= 4 then
    int_of_string argv.(3)
  else
    n_individuals / 10 ;;

assert (n_species > 0) ;;

let synthesize =
  Array.length argv >= 5 && argv.(4) = "--synthesize" ;;

let ineq =
  Array.length argv >= 6 && argv.(5) = "--ineq" ;;

(* schema *)

type bird = (
  Int,  (* individual ID *)
  Int   (* bird type ID *)
) Schema ;;

type observation = (
  Int,  (* longitude (X), always multiplied by 100 *)
  Int,  (* latitude (Y), always multiplied by 100 *)
  Int,  (* individual ID *)
  Int,  (* timestamp *)
  Int   (* observation ID *)
) Schema ;;

let point_noise = 10 ;;

(* constant values for somewhat reasonable geography *)

(* departure from Mexico *)

let x_orig = - 100_00  ;;  (* inclusive *)

let y_orig =    20_00  ;;  (* exclusive *)

(* now in Pennsylvania *)

let x_now  = -  80_00  ;;  (* inclusive *)

let y_now  =    40_00  ;;  (* exclusive *)

assert
  (x_orig % 100 = 0 && y_orig % 100 = 0 && 
      x_now % 100 = 0 && y_now % 100 = 0) ;;

(* wrappers around RNG *)

let random_x_around x =
  (x - point_noise) + random_int (2 * point_noise + 1) ;;

let random_y_around y =
  (y - point_noise) + random_int (2 * point_noise + 1) ;;

let random_pair_around (x, y) =
  random_x_around x, random_y_around y ;;

let random_point_for_t t =
  random_pair_around
    (x_orig + (x_now - x_orig) * t / 100,
     y_orig + (y_now - y_orig) * t / 100) ;;

let random_species () =
  random_int n_species ;;

let random_individual () =
  random_int n_individuals ;;

let birds =
  let f i =
    let s = random_species () in
    make_row_bird (toi i, toi s) in
  make_db_bird (List.init n ~f) ;;

let l_observations =
  let f i =
    let t = i / (n / 100) in
    let j = random_individual ()
    and x, y = random_point_for_t t in
    make_row_observation (toi x, toi y, toi j, toi t, toi i) in
  List.init n ~f ;;

let l_observations =
  if not synthesize then
    l_observations
  else
    let x = fresh_int_var ()
    and y = fresh_int_var ()
    and j = fresh_int_var ()
    and t = fresh_int_var ()
    and i = fresh_int_var () in
    constrain (~logic (t > 100 && i >= toi n));
    make_row_observation (x, y, j, t, i) :: l_observations ;;

let observations = make_db_observation l_observations ;;

let observations_species =
  let f (id, _,
         _, _, id', _, _ : Row) = ~logic (id = id') in
  ~logic (sel (cross birds observations) f) ;;

let looking_for_species = toi (random_species ()) ;;

let in_area x y =
  if ineq then
    ~logic (x + 2 * y >= 3_00)
  else
    ~logic (x >= -79_00 && y >= 41_00) ;;

constrain
  (let f (_, s, x, y, _, _, _ : Row) =
     ~logic (in_area x y && s = looking_for_species) in
   ~logic (exists (sel (cross observations birds) f))) ;;

solve_print_result () ;;
