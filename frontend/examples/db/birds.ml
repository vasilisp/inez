open Core.Std ;;
open Db_eager_script ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

type bird = (Int, Int, Int) Schema ;;

type env = (Int, Int, Int) Schema ;;

type quarter_space = (Int, Int) Schema ;;

let birds =
  make_db_bird
    (List.map ~f:make_row_bird
       (~logic [1167631, 43, 70;
                1088864, 43, 411;
                2701077, 43, 53;
                1106829, 43, 100;
                2901155, 43, 65;
                3229001, 43, 110;
                3229272, 43, 150;
                3222976, 43, 75;
                1095884, 43, 67;
                1105308, 43, 946;
                4544086, 43, 70;
                1120576, 43, 100;
                1097445, 43, 67;
                1094715, 43, 100])) ;;

let env =
  make_db_env
    (List.map ~f:make_row_env
       (~logic [1167631, 33, -117;
                1088864, 34, -107;
                2701077, 34, -117;
                1106829, 34, -118;
                2901155, 34, -97;
                3229001, 35, -119;
                3229272, 35, -119;
                3222976, 35, -118;
                1095884, 36, -105;
                1105308, 39, -97;
                4544086, 41, -89;
                1120576, 43, -79;
                1097445, 43, -89;
                1094715, 43, -72])) ;;

let y = fresh_int_var () ;;

let qs =
  make_rel_quarter_space
    (fun (x', y' : Row) -> ~logic (x' >= 30 && y' >= y))
;;

let cp =
  ~logic
    (sel (cross qs (cross env birds))
       (fun (y1, x1, id, y2, x2, id', _, _ : Row) ->
         x1 = x2 && y1 = y2 && id = id')) ;;

constrain
  (~logic
      (exists
         (sel cp
            (fun (_, _, _, _, _, _, y, n : Row) ->
              y = 43 && n >= 500)))) ;;

minimize (~logic (- y)) ;;

print_endline (string_of_result (solve ())) ;;

ideref_print "y" y ;;
