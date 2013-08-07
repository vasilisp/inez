open Core.Std ;;
open Db_eager_script ;;

type project = (
  Int, (* ID *)
  Int  (* Manager ID *)
) Schema ;;

type manager = (
  Int, (* ID *)
  Int  (* Age *)
) Schema ;;

let n = 2000 ;;

(* project_ids = [v_0; v_1; ...; v_{n - 1}] *)

let project_ids = List.init n ~f:(fun _ -> fresh_int_var ()) ;;

(* projects = [0, v_0; 1, v_1; ...; n - 1, v_{n - 1}] *)

let projects =
  let f i v = make_row_project (toi i, v) in
  make_db_project (List.mapi project_ids ~f) ;;
  
let managers =
  make_db_manager
    (List.map ~f:make_row_manager
       (~logic
           [1000, 40;
            1010, 34;
            1020, 48;
            1040, 29;
            1050, 38;
            1060, 40;
            1070, 34;
            1080, 48;
            1090, 29;
            1100, 38;
           ])) ;;

(* every manager manages something *)

constrain
  (~logic
      (not (exists
              (sel managers (fun (id, _ : Row) ->
                not (exists
                       (sel projects (fun (_, mid : Row) ->
                         mid = id)))))))) ;;

(* foreign key constraint *)

constrain
  (~logic
      (not (exists
              (sel projects (fun (_, mid : Row) ->
                not (exists
                       (sel managers (fun (id, _ : Row) ->
                         mid = id)))))))) ;;

print_endline (string_of_result (solve ())) ;;

print_string "project_ids:\n" ;;

List.iteri project_ids
  ~f:(fun i v ->
    match ideref v with
    | Some x ->
      Printf.printf "v_%d = %s\n" i (Int63.to_string_hum x)
    | None ->
      ()) ;;
