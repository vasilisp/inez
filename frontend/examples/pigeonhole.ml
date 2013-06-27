open Script_solver ;;

open Core.Std ;;

let make_map l_p l_h =
  let hp_map =
    let size = List.length l_p * List.length l_h in
    Hashtbl.Poly.create ~size () in
  List.iter l_p ~f:(fun p ->
    List.iter l_h ~f:(fun h ->
      let v = fresh_int_var () in
      constrain (~logic (v >= 0));
      constrain (~logic (v <= 1));
      let key = p, h and data = v in
      Hashtbl.replace hp_map ~key ~data));
  fun p h -> Hashtbl.find_exn hp_map (p, h) ;;

(* problem definition *)

let n = 20 ;;
assert (n >= 1) ;;

(* entities *)

type hole    =  { h_id: int } ;;
type pigeon  =  { p_id: int } ;;

(* entity instances *)

let holes    =  List.init (n - 1) ~f:(fun h_id -> {h_id}) ;;
let pigeons  =  List.init n       ~f:(fun p_id -> {p_id}) ;;

(* map from pigeons to holes *)

let m = make_map pigeons holes ;;

(* each pigeon goes to one hole *)

constrain
  (~logic (forall pigeons ~f:(fun p -> sum holes ~f:(m p) = 1))) ;;

(* each hole contains one pigeon *)

constrain
  (~logic
      (forall holes
         ~f:(fun h -> sum pigeons ~f:(Fn.flip m h) = 1))) ;;

print_endline (string_of_result (solve ())) ;;
