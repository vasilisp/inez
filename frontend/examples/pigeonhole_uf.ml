open Core.Std
open Script_init

(* parameters *)

let n_pigeons = 7 ;;
let n_holes = n_pigeons - 1 ;;

assert (n_pigeons >= 0) ;;
assert (n_holes >= 0) ;;

(* problem entities and instances *)

type pigeon = { p_id: int } ;;

let pigeons = List.init n_pigeons ~f:(fun p_id -> {p_id}) ;;

(* UF: pigeons to holes *)

let m =
  let um (x : Int) = ~free in
  fun {p_id} -> um (toi p_id) ;;

(* constraints *)

(* each pigeon goes to some hole *)

let g =
  Formula.forall pigeons
    ~f:(fun p -> ~logic (m p >= 1 && m p <= toi n_holes)) ;;

(* no pair of pigeons co-inhabit a hole *)

let h =
  Formula.forall_pairs pigeons
    ~f:(fun p1 p2 -> ~logic (not (m p1 = m p2))) ;;

(* call solver *)

constrain g ;;
constrain h ;;

let _ = 
  let open Terminology in
  match solve () with
  | R_Unsat ->
    Printf.printf "unsat\n%!"
  | R_Opt | R_Unbounded | R_Sat ->
    Printf.printf "sat\n%!"
  | R_Unknown ->
    Printf.printf "unknown\n%!"
