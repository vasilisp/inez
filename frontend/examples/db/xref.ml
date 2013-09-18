open Core.Std ;;
open Db_eager_script ;;

let n =
  if Array.length Sys.argv >= 4 then
    int_of_string Sys.argv.(2)
  else
    8 ;;

let k =
  if Array.length Sys.argv >= 4 then
    int_of_string Sys.argv.(3)
  else
    4 ;;

let behavior =
  if Array.length Sys.argv >= 5 then
    match Sys.argv.(4) with
    | "--synthesize" ->
      `Synthesize
    | "--easy-sat" ->
      `Easy_sat
    | _ ->
      `Unsat
  else
    `Unsat ;;

assert (k >= 0) ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    ()

type ii = (Int, Int) Schema ;;

let db0 =
  make_db_ii
    (let f i = make_row_ii (~logic (toi i, 0)) in
     List.init n ~f)

let db1 =
  let l =
    let f i = make_row_ii (toi (i % n), toi i) in
    List.init (n * k) ~f in
  let l =
    match behavior with
    | `Synthesize ->
      make_row_ii (fresh_int_var (), fresh_int_var ()) :: l
    | _ ->
      l in
  make_db_ii l

let exists_m_in_db1 x m =
  let rec f acc = function
    | a :: ((ad :: _) as d) ->
      f (~logic (a < ad && acc)) d
    | _ ->
      acc
  and lv = List.init m ~f:(fun _ -> fresh_int_var ()) in
  ~logic (f true lv &&
            let f v =
              let f (x', v' : Row) = x = x' && v = v' in
              exists (sel db1 f) in
            forall lv ~f) ;;

constrain
  (let k = match behavior with `Easy_sat -> k | _ -> k + 1 in
   ~logic (exists
             (let f (x, _ : Row) = exists_m_in_db1 x k in
              sel db0 f))) ;;

print_endline (string_of_result (solve ())) ;;
