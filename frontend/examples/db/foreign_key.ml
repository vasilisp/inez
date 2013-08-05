open Core.Std ;;
open Db_script ;;

type project = (
  Int, (* ID *)
  Int  (* Manager ID *)
) Schema ;;

type manager = (
  Int, (* ID *)
  Int  (* Age *)
) Schema ;;

(* project_ids = [v_0; v_1; ...; v_99] *)

let project_ids = List.init 200 ~f:(fun _ -> fresh_int_var ()) ;;

(* projects = [0, v_0; 1, v_1; ...; 99, v_99] *)

let projects =
  let f i v = make_row_project (toi i, v) in
  make_db_project (List.mapi project_ids ~f) ;;
  
let managers =
  make_db_manager
    (List.map ~f:make_row_manager
       (~logic [1000, 40;
                1010, 34;
                1020, 48;
                1040, 29;
                1050, 55])) ;;

(* foreign key constraint *)

constrain
  (~logic
      (not (exists
              (sel projects (fun (_, mid : Row) ->
                not (exists
                       (sel managers (fun (id, _ : Row) ->
                         mid = id)))))))) ;;

(* every manager manages something *)

constrain
  (~logic
      (not (exists
              (sel managers (fun (id, _ : Row) ->
                not (exists
                       (sel projects (fun (_, mid : Row) ->
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
