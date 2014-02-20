open Script ;;
open Core.Std ;;

(* utils *)

let iob x = ~logic (iite x 1 0) ;;

(* types *)

type processor = {
  p_id      :  int;
  p_ram     :  int;
  p_cycles  :  int;
} ;;

type job = {
  j_id      :  int;
  j_ram     :  int;
  j_cycles  :  int;
  j_sep     :  job list;
} ;;

(* data *)

let p0 = {p_id = 0; p_ram = 256; p_cycles = 1000000} ;;
let p1 = {p_id = 1; p_ram = 256; p_cycles = 1000000} ;;
let p2 = {p_id = 2; p_ram = 256; p_cycles = 1000000} ;;
let p3 = {p_id = 3; p_ram = 256; p_cycles = 1000000} ;;

let processors = [p0; p1; p2; p3] ;;

let j0 = {j_id = 0; j_ram = 64; j_cycles = 200000; j_sep = []} ;;
let j1 = {j_id = 1; j_ram = 128; j_cycles = 200000; j_sep = []} ;;
let j2 = {j_id = 2; j_ram = 32; j_cycles = 400000; j_sep = []} ;;
let j3 = {j_id = 3; j_ram = 128; j_cycles = 400000; j_sep = []} ;;
let j4 = {j_id = 4; j_ram = 64; j_cycles = 200000; j_sep = []} ;;
let j5 = {j_id = 5; j_ram = 128; j_cycles = 200000; j_sep = []} ;;
let j6 = {j_id = 6; j_ram = 32; j_cycles = 400000; j_sep = []} ;;
let j7_0 =
  {j_id = 7; j_ram = 128; j_cycles = 200000; j_sep = []} ;;
let j7_1 =
  {j_id = 17; j_ram = 128; j_cycles = 200000; j_sep = [j7_0]} ;;

let jobs = [j0; j1; j2; j3; j4; j5; j6; j7_0; j7_1] ;;

let (-->) =
  let h = Hashtbl.Poly.create () in
  let default () = fresh_bool_var () in
  fun j p -> Hashtbl.find_or_add h (j, p) ~default ;;

(*
let (-->) =
  let um _ _ = (~free : Bool) in
  fun {j_id} {p_id} -> um (toi j_id) (toi p_id) ;;
*)

(* map each job somewhere *)

constrain
  (~logic (forall jobs
             ~f:(fun j ->
               let s = sum processors ~f:(fun p -> iob (j --> p)) in
               s = 1))) ;;

(* RAM resource constraints *)

let consumed_ram ({j_ram} as j) p =
  ~logic (iite (j --> p) (toi j_ram) 0) ;;

constrain
  (~logic
      (forall processors
         ~f:(fun ({p_ram} as p) ->
           let s = sum jobs ~f:(fun j -> consumed_ram j p) in
           s <= toi p_ram))) ;;

(* CPU resource constraints *)

let consumed_cycles ({j_cycles} as j) p =
  ~logic (iite (j --> p) (toi j_cycles) 0) ;;

constrain
  (~logic
      (forall processors
         ~f:(fun ({p_cycles} as p) ->
           let s = sum jobs ~f:(fun j -> consumed_cycles j p) in
           s <= toi p_cycles))) ;;

(* separation constraints *)

constrain
  (~logic
      (forall jobs
         ~f:(fun ({j_sep} as j) ->
           forall j_sep
             ~f:(fun j2 ->
               forall processors
                 ~f:(fun p ->
                   j --> p => not (j2 --> p)))))) ;;

(* solve *)

print_endline (string_of_result (solve ())) ;;

let processor_of_job j = 
  match
    let f p = Option.value_exn (bderef (j --> p)) in
    List.find processors ~f
  with
  | Some {p_id} -> p_id
  | None -> -1 ;;

List.iter jobs
  ~f:(fun ({j_id} as j) ->
    Printf.printf "p%d: %d\n%!" j_id (processor_of_job j)) ;;
