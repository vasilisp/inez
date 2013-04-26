(* utilities *)

let rec make_n ?acc:(acc = []) n ~f =
  if n <= 0 then
    List.rev acc
  else
    make_n ~acc:(f n :: acc) (n - 1) ~f;;

let sum ~f =
  List.fold_left ~init:(logic(0))
    ~f:(fun acc x -> logic (acc + f x));;

let make_map l_p l_h =
  let hp_map =
    let size = List.length l_p * List.length l_h in
    Hashtbl.Poly.create ~size () in
  List.iter l_p ~f:(fun p ->
    List.iter l_h ~f:(fun h ->
      let v = fresh_int_var () in
      constrain (logic (v >= 0));
      constrain (logic (v <= 1));
      Hashtbl.replace hp_map (p, h) v));
  fun p h -> Hashtbl.find_exn hp_map (p, h);;

(* problem definition *)

let n = 20;;
assert (n >= 1);;

(* entities *)

type hole    =  { h_id: int };;
type pigeon  =  { p_id: int };;

(* entity instances *)

let holes    =  make_n (n - 1) ~f:(fun h_id -> {h_id});;
let pigeons  =  make_n n       ~f:(fun p_id -> {p_id});;

(* map from pigeons to holes *)

let m = make_map pigeons holes;;

(* each pigeon goes to one hole *)

constrain
  (Formula.forall pigeons
     ~f:(fun p -> logic (sum holes ~f:(m p) = 1)));;

(* each hole contains one pigeon *)

constrain
  (Formula.forall holes
     ~f:(fun h -> logic (sum pigeons ~f:(Fn.flip m h) = 1)));;

solve ();;
