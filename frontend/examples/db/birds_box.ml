(* benchmark for "ILP Modulo Data" (http://arxiv.org/abs/1404.5665) *)

open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|15038; 19624; 31779; 2891; 13009|] ;;

let random_int = Random.State.int state ;;

(* input *)

let n_observations =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    1000 ;;

assert (n_observations > 0) ;;

let n_types =
  if Array.length argv >= 3 then
    int_of_string argv.(2)
  else
    n_observations / 10 ;;

assert (n_types > 0 && n_types < n_observations) ;;

let n_in_box =
  if Array.length argv >= 4 then
    int_of_string argv.(3)
  else
    12 * n_observations / (10 * n_types) ;;

assert (n_in_box >= 2) ;;

(* schema *)

type observation = (
  Int,  (* observation ID *)
  Int,  (* bird type ID *)
  Int,  (* longitude (X) *)
  Int   (* latitude (Y) *)
) Schema ;;

(* constant values for somewhat reasonable geography *)

let x_min = 75   ;;  (* inclusive *)

let x_max = 105  ;;  (* exclusive *)

let y_min = 30   ;;  (* inclusive *)

let y_max = 55   ;;  (* exclusive *)

let min_x_range_for_type = 2  ;;

let min_y_range_for_type = 2  ;;

let max_x_range_for_type = 20  ;;

let max_y_range_for_type = 10  ;;

(* wrappers around RNG *)

let random_type () =
  random_int n_types ;;

let random_x () =
  x_min + random_int (x_max - x_min) ;;

let random_y () =
  y_min + random_int (y_max - y_min) ;;

let random_pair () =
  random_x (), random_y ()

(* observations for a particular kind of bird centered around a (x, y)
   pair *)

let centers_h =
  let rval = Int.Table.create () ~size:(2 * n_types) in
  for key = 0 to n_types do
    let data = random_pair () in
    Hashtbl.replace rval ~key ~data
  done;
  rval ;;

(* range for ys *)

let ranges_h =
  let rval = Int.Table.create () ~size:(2 * n_types) in
  for key = 0 to n_types do
    let x =
      min_x_range_for_type +
        random_int (max_x_range_for_type - min_x_range_for_type)
    and y =
      min_y_range_for_type +
        random_int (max_y_range_for_type - min_y_range_for_type) in
    Hashtbl.replace rval ~key ~data:(x, y)
  done;
  rval ;;

let rec random_point_for_type ?n:(n = 0) t =
  assert (n <= 100);
  let (center_x, center_y) as center = Hashtbl.find_exn centers_h t
  and range_x, range_y = Hashtbl.find_exn ranges_h t in
  let x = center_x - range_x / 2 + random_int range_x
  and y = center_y - range_y / 2 + random_int range_y in
  if x_min <= x && x < x_max && y_min <= y && y < y_max then
    x, y
  else if n = 10 then
    center
  else
    random_point_for_type t ~n:(n + 1)

let observations =
  let f _ =
    let t = random_type () in
    let x, y = random_point_for_type t in
    t, x, y
  and cmp (_, x1, _) (_, x2, _) = Int.compare x1 x2 in
  List.sort (List.init n_observations ~f) ~cmp ;;

let observations =
  make_db_observation
    (let f i (t, x, y) =
       make_row_observation (~logic (toi i, toi t, toi x, toi y)) in
     List.mapi observations ~f) ;;

(* we are going to compute a box *)

let b_x_min = fresh_int_var () ;;

let b_x_max = fresh_int_var () ;;

constrain (~logic (b_x_max >= b_x_min)) ;;

let b_y_min = fresh_int_var () ;;

let b_y_max = fresh_int_var () ;;

constrain (~logic (b_y_max >= b_y_min)) ;;

let mk_unequal_variables n =
  let rec f acc = function
    | a :: ((ad :: _) as d) ->
      f (~logic (a < ad && acc)) d
    | _ ->
      acc in
  let l = let f _ = fresh_int_var () in List.init n ~f in
  constrain (~logic (f true l)); l

(* the box contains [n_in_box] distinct observations of the same kind
   of bird *)

(* bird type ID for the [n_in_box] observations *)

let t0 = fresh_int_var () ;;

let f v =
  let f (id, t, x, y : Row) =
    ~logic (id = v &&
        t0 = t &&
        b_x_min <= x && x < b_x_max &&
        b_y_min <= y && y < b_y_max) in
  constrain (~logic (exists (sel observations f))) in
List.iter (mk_unequal_variables n_in_box) ~f ;;

solve_print_result () ;;

(*

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

ideref_print "x_min" b_x_min ;;

ideref_print "x_max" b_x_max ;;

ideref_print "y_min" b_y_min ;;

ideref_print "y_max" b_y_max ;;

*)
