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

let n_types =
  if Array.length argv >= 3 then
    int_of_string argv.(2)
  else
    10 ;;

let unsat =
  if Array.length argv >= 4 then
    argv.(3) = "--unsat"
  else
    false ;;

assert (n_types >= 0) ;;

(* assert (n_types <= (n / 100)) ;; *)

(* schema *)

(* longitudes and latitudes multiplied by 100 *)

type observation = (
  Int,  (* timestamp *)
  Int,  (* bird type ID *)
  Int,  (* longitude (X) *)
  Int,  (* latitude (Y) *)
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

let random_type () =
  random_int n_types ;;

let l_observations =
  let f i =
    let t = i / (n / 100) in
    let p = random_type ()
    and x, y = random_point_for_t t in
    make_row_observation (toi t, toi p, toi x, toi y, toi i) in
  List.init n ~f ;;

let l_observations =
  if unsat then
    l_observations
  else
    let f i =
      let t = fresh_int_var ()
      and p = fresh_int_var ()
      and x = fresh_int_var ()
      and y = fresh_int_var ()
      and i = toi (n + i) in
      constrain (~logic (x > toi x_now && y > toi y_now &&
                           t > 100 &&
                           p >= 0 && p <= toi n_types));
      make_row_observation (t, p, x, y, i) in
    List.init 5 ~f @ l_observations ;;

let observations = make_db_observation l_observations ;;

let oo =
  ~logic
    (sel (cross observations observations)
       (fun (_, p , _, _, _,
             _, p', _, _, _ : Row) ->
         p = p')) ;;

let ooo =
  ~logic
    (sel (cross oo observations)
       (fun (_, p , _, _, _,
             _, _ , _, _, _,
             _, p', _, _, _ : Row) ->
         p = p')) ;;

constrain
  (~logic
      (exists
         (sel ooo
            (fun (t0, _, x0, y0, _,
                  t1, _, x1, y1, _,
                  t2, _, x2, y2, _ : Row) ->
              x2 > toi x_now && y2 > toi y_now &&
                t2 > 100 && 100 > t1 && t1 > t0 &&
                x2 >= x1 && x1 >= x0 &&
                y2 >= y1 && y1 >= y0 &&
                2 * (t2 - t0) <= 5 * (t1 - t0) &&
                2 * (t2 - t0) >= 3 * (t1 - t0) &&
                2 * (x2 - x0) <= 5 * (x1 - x0) &&
                2 * (x2 - x0) >= 3 * (x1 - x0) &&
                2 * (y2 - y0) <= 5 * (y1 - y0) &&
                2 * (y2 - y0) >= 3 * (y1 - y0))))) ;;

solve_print_result () ;;
