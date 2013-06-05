open Db_lang_abstract

let ideref_human x =
  Option.(ideref x >>= Int63.to_int) ;;

let make_entry (a, b) =
  R.R_Pair (R.R_Int a, R.R_Int b) ;;

let make_db l =
  D.D_Input (S.S_Pair (S.S_Int, S.S_Int), List.map l ~f:make_entry) ;;

let v = fresh_int_var () ;;

let u = fresh_int_var () ;;

let db = make_db
  [toi 12, toi 12;
   toi 23, v;
   toi 32, u] ;;

constrain
  (exists
     (sel db
        (fun (R.R_Pair (_, R.R_Int x)) ->
          Formula.F_Atom (A.A_Eq (M.(x + toi 1821)))))) ;;

constrain
  (Formula.F_Atom (A.A_Eq (M.(v + toi 18)))) ;;

solve () ;;

ideref_human v ;;

ideref_human u ;;
