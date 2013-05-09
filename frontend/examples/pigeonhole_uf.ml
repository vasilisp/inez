(* parameters *)

let n_pigeons = 10;;
let n_holes = n_pigeons - 1;;

assert (n_pigeons >= 0);;
assert (n_holes >= 0);;

(* utilities *)

let rec make_n ?acc:(acc = []) n ~f =
  if n <= 0 then
    List.rev acc
  else
    make_n ~acc:(f n :: acc) (n - 1) ~f;;

(* problem entities and instances *)

type pigeon = { p_id: int };;

let pigeons = make_n n_pigeons ~f:(fun p_id -> {p_id});;

(* UF: pigeons to holes *)

let m =
  let um = uf (x: int) -> int in
  fun {p_id} -> um (toi p_id);;

(* constraints *)

(* each pigeon goes to some hole *)

let g =
  Formula.forall pigeons
    ~f:(fun p -> logic (m p >= 1 && m p <= toi n_holes));;

(* no pair of pigeons co-inhabit a hole *)

let h =
  Formula.forall_pairs pigeons
    ~f:(fun p1 p2 -> logic (not (m p1 == m p2)));;

(* call solver *)

constrain g;;
constrain h;;
solve ();;
