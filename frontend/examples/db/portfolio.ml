(* benchmark for "ILP Modulo Data" (http://arxiv.org/abs/1404.5665) *)

open Core.Std ;;
open Db_script ;;

let state = Random.State.make [|215143; 6764; 936217; 435|] ;;

let random_int = Random.State.int state ;;

let random_bool () = Random.State.bool state ;;

let tob b = ~logic (if b then true else false) ;;

let n_portfolio =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    5 ;;

let n_stocks =
  if Array.length argv >= 3 then
    int_of_string argv.(2)
  else
    500 ;;

(* hard-coded constants *)

let n_sectors = 5 ;;

type stock = (
  Int,   (* ID *)
  Bool,  (* small capitalization *)
  Int    (* sector ID *)
) Schema ;;

type price = (
  Int,  (* ID *)
  Int,  (* price *)
  Int   (* year *)
) Schema ;;

type dividend = (
  Int,  (* ID *)
  Int   (* amount *)
) Schema ;;

let l_pdcs =
  let l =
    let f _ =
      50 + random_int 100,     (* _p_rice for 2014 *)
      random_int 20,           (* _d_ividend *)
      random_bool (),          (* _c_apitalization is small *)
      random_int n_sectors in  (* _s_ector *)
    List.init n_stocks ~f
  (* and cmp (p, d, _, _) (p', d', _, _) = *)
  (*   Int.compare (p' + d') (p + d) in *)
  and cmp (p, _, _, _) (p', _, _, _) = Int.compare p' p in 
  List.sort l ~cmp ;;

let db_stocks =
  let f i (_, _, cap, sector) =
    make_row_stock (toi i, tob cap, toi sector) in
  make_db_stock (List.mapi l_pdcs ~f) ;;

let db_prices =
  (*
  let l_2013 =
    let f i = make_row_price (toi i, ~logic 100, ~logic 2013) in
    List.init n_stocks ~f
  *)
  let l_2014 =
    let f i (p, _, _, _) = make_row_price (toi i, toi p, ~logic 2014) in
    List.mapi l_pdcs ~f in
  make_db_price l_2014 ;;

let db_dividends =
  let f i (_, d, _, _) = make_row_dividend (toi i, toi d) in
  make_db_dividend (List.mapi l_pdcs ~f) ;;

let iter_pairs l ~f =
  let rec iter_pairs_aux = function
    | a :: d ->
      Core.Std.List.iter d ~f:(f a); iter_pairs_aux d
    | [] ->
      () in
  iter_pairs_aux l

let portfolio_ids =
  let l =
    let f _ = fresh_int_var () in
    List.init n_portfolio ~f in
  let _ =
    let f v1 v2 = constrain (~logic (not (v1 = v2))) in
    iter_pairs l ~f in
  l ;;

let portfolio =
  let f i id =
    let db = ~logic (cross (cross db_stocks db_prices) db_dividends)
    and cap = fresh_bool_var ()
    and sector = fresh_int_var ()
    and price = fresh_int_var ()
    and shares = Int63.(of_int 5 * (of_int n_portfolio - of_int i))
    and dividend = fresh_int_var () in
    let f (id0, (cap' : Bool), sector',
           id1, price', year,
           id2, dividend' :
             Row) =
      ~logic
        (id = id0 && sector = sector' &&
            (cap => cap' && cap' => cap) &&
            id = id1 && price = price' && year = 2014 &&
            id = id2 && dividend = dividend') in
    ~logic (sel db f |> exists) |> constrain;
    id, cap, sector, shares, price, dividend in
  List.mapi portfolio_ids ~f ;;

let total_capital =
  let f acc (_, _, _, s, _, _) = Int63.(acc + s * of_int 100)
  and init = Int63.of_int 0 in
  List.fold_left portfolio ~f ~init ;;

let _ =
  let n = n_portfolio / 2
  and f (_, b, _, _, _, _) = ~logic (iite b 1 0) in
  let s = ~logic (sum portfolio ~f) in
  constrain (~logic (s <= toi n)) ;;

let objective =
  let f (_, _, _, s, p, d) = ~logic (s * (p + d)) in
  ~logic (- (sum portfolio ~f)) ;;

minimize objective ;;

for i = 0 to n_sectors do
  let f (_, _, e, s, p, d) =
    ~logic (iite (e = toi i) (s * (p + d)) 0)
  and rhs = toi63 Int63.(total_capital / of_int 2) in
  constrain (~logic (sum portfolio ~f <= rhs))
done ;;

solve_print_result () ;;
