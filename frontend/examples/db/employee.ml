open Core.Std ;;
open Db_script ;;

let state = Random.State.make [215143; 6764; 936217; 435] ;;

let random_int = Random.State.int state ;;

type employee = (
  Int,  (* ID *)
  Bool  (* true iff manager *)
) Schema ;;

type project = (
  Int,  (* ID *)
  Int   (* Project Manager ID *)
) Schema ;;

type membership = (
  Int,  (* Project ID *)
  Int   (* Employee ID *)
) Schema ;;

let n_employees =
  if Array.length Sys.argv >= 6 then
    int_of_string Sys.argv.(2)
  else
    100 ;;

let n_managers =
  if Array.length Sys.argv >= 6 then
    int_of_string Sys.argv.(3)
  else
    20 ;;

let max_projects_per_manager =
  if Array.length Sys.argv >= 6 then
    int_of_string Sys.argv.(4)
  else
    5 ;;

let max_members_per_project =
  if Array.length Sys.argv >= 6 then
    int_of_string Sys.argv.(5)
  else
    10 ;;

let synthesize =
  Array.length Sys.argv >= 7 && Sys.argv.(6) = "--synthesize" ;;

let goal =
  max_projects_per_manager * max_members_per_project + 1;;

type ugen = {
  u_gen     :  unit -> int;
  u_exists  :  int -> bool;
} ;;

let make_ugen n =
  let h = Int.Table.create () ~size:(n / 2) in
  let rec u_gen () =
    let i = random_int n in
    match Hashtbl.find h i with
    | Some _ ->
      u_gen ()
    | None ->
      Int.Table.add_exn h ~key:i ~data:true; i
  and u_exists i = Option.is_some (Hashtbl.find h i) in
  {u_gen; u_exists} ;;

let ugen_employees =
  make_ugen ((n_employees + n_managers) * 2) ;;

let ugen_projects =
  make_ugen ((n_managers * max_projects_per_manager) * 2) ;;

let employee_ids =
  let {u_gen} = ugen_employees in
  let f _ = u_gen () in
  List.init n_employees ~f ;;

let random_employee_id () =
  let n = List.length employee_ids in
  let n = random_int n in
  List.nth_exn employee_ids n

let manager_ids =
  let {u_gen} = ugen_employees in
  let f _ = u_gen () in
  List.init n_managers ~f ;;

let employees =
  let l_employees =
    let f i = make_row_employee (toi i, ~logic false) in
    List.map employee_ids ~f
  and l_managers =
    let f i = make_row_employee (toi i, ~logic true) in
    List.map manager_ids ~f in
  make_db_employee (l_managers @ l_employees) ;;

let make_project =
  let {u_gen} = ugen_projects in
  fun mid ->
    let pid = u_gen () in
    make_row_project (toi pid, toi mid), pid ;;

let projects, project_ids =
  let {u_gen = f} = ugen_projects in
  let f _ = f () in
  List.fold_left manager_ids ~init:([], [])
    ~f:(fun (lp, li) mid ->
      let mid = toi mid in
      let n = random_int (max_projects_per_manager + 1) in
      let project_ids = List.init n ~f
      and f pid = make_row_project (toi pid, mid) in
      let projects = List.map project_ids ~f in
      projects @ lp, project_ids @ li) ;;

let projects = make_db_project projects ;;

let memberships =
  List.fold_left project_ids
    ~init:[]
    ~f:(fun acc pid ->
      let pid = toi pid in
      let n = random_int (max_members_per_project + 1) in
      List.init n
        ~f:(fun _ ->
          let eid = toi (random_employee_id ()) in
          make_row_membership (pid, eid)) @ acc) ;;

let memberships =
  if not synthesize then
    memberships
  else
    let f _ =
      let v1 = fresh_int_var ()
      and v2 = fresh_int_var () in
      make_row_membership (v1, v2) in
    List.init goal ~f @ memberships ;;

let memberships = make_db_membership memberships ;;

let mk_unequal_variables m =
  let rec f acc = function
    | a :: ((ad :: _) as d) ->
      f (~logic (a < ad && acc)) d
    | _ ->
      acc in
  let l = let f _ = fresh_int_var () in List.init m ~f in
  l, ~logic (f true l) ;;

let has_m_managees m mid =
  let f x =
    let f (pid, mid', pid2, eid : Row) =
      ~logic (mid = mid' && pid = pid2 && eid = x) in
    ~logic (exists (sel (cross projects memberships) f))
  and l, g = mk_unequal_variables m in
  ~logic (g && forall l ~f) ;;

constrain 
  (let f (eid, (mgr : Bool) : Row) =
     ~logic (mgr && has_m_managees goal eid) in
   ~logic (exists (sel employees f))) ;;

print_endline (string_of_result (solve ())) ;;
