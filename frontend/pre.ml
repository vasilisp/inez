open Core.Std
open Terminology
open Lang_abstract

module Make (I : Lang_ids.Accessors) = struct

  type fun_id = I.c Lang_ids.Box_arrow.t

  let compare_fun_id x y =
    Lang_ids.Box_arrow.compare I.compare_c x y

  let fun_id_of_sexp x =
    raise (Unreachable.Exn _here_)

  let sexp_of_fun_id =
    Lang_ids.Box_arrow.sexp_of_t I.sexp_of_c

  type ibflat =
    (term, formula) Terminology.ibeither

  (* Some of the definitions below look pedantic, but it is useful to
     have the corresponding compare_* functions around. *)

  and args =
    ibflat list

  and app =
    fun_id * args

  and sumt =
    Int63.t * term_base

  and sum =
    sumt list

  and iite =
    formula * term * term

  and term_base =
  | B_Var   of  (I.c, int) Lang_ids.t
  | B_App   of  app
  | B_Ite   of  iite

  and term =
  | G_Base  of  term_base
  | G_Sum   of  sum Terminology.offset

  and bite = formula * formula * formula

  and formula =
  | U_Var   of  (I.c, bool) Lang_ids.t
  | U_Atom  of  term * op'
  | U_Not   of  formula
  | U_And   of  formula list
  | U_App   of  app
  | U_Ite   of  bite

  with compare, sexp_of

  module Sum = struct
    module T = struct
      type t = sum
      let compare = compare_sum
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_sum
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  module Args = struct
    module T = struct
      type t = args
      let compare = compare_args
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_args
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  module Iite = struct
    module T = struct
      type t = iite
      let compare = compare_iite
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_iite
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  let dummy_formula = U_And []

  type ctx = {
    r_sum_h       :  sum Sum.Table.t;
    r_args_h      :  args Args.Table.t;
    r_iite_h      :  term_base Iite.Table.t;
  }

  let make_ctx () = {
    r_sum_h = Sum.Table.create ();
    r_args_h = Args.Table.create ();
    r_iite_h = Iite.Table.create ();
  }

  (* we will expand-out ITE right before blasting *)
  let ff_ite q g h =
    let ff_not = function U_Not g -> g | g -> U_Not g in
    let ff_or a b = U_Not (U_And [ff_not a; ff_not b]) in
    U_And [ff_or (ff_not q) g; ff_or q h]

  let sum_negate (l, x) =
    List.map l ~f:(Tuple.T2.map1 ~f:Int63.neg), Int63.neg x

  (*
    let int_term_minus a b =
    match a, b with
    | G_Base a, G_Base b ->
    G_Sum ([Int63.one, a; Int63.minus_one, b], Int63.zero)
    | G_Sum (l, x), G_Base b ->
    G_Sum ((Int63.minus_one, b) :: l, x)
    | G_Base b, G_Sum s ->
    let l, x = sum_negate s in
    G_Sum ((Int63.one, b) :: l, x)
    | G_Sum (l, x), G_Sum s ->
    let l2, x2 = sum_negate s in
    G_Sum (List.append l l2, Int63.(x + x2))
  *)

  (* flatten terms and formulas; SCC impractical to break *)
  let dedup_sum l =
    let l = List.sort ~cmp:compare_sumt l in
    let rec loop ~acc = function
      | [] ->
        acc
      | hd :: [] ->
        hd :: acc
      | (c1, m1) :: (c2, m2) :: d when compare_term_base m1 m2 = 0 ->
        loop ~acc ((Int63.(c1 + c2), m1) :: d)
      | (c, m) :: d when c = Int63.zero ->
        loop ~acc d
      | a :: d ->
        loop ~acc:(a :: acc) d in
    loop ~acc:[] l

  let make_sum {r_sum_h} l o =
    let l = dedup_sum l in
    Hashtbl.find_or_add r_sum_h l ~default:(fun () -> l), o

  let make_args {r_args_h} l =
    Hashtbl.find_or_add r_args_h l ~default:(fun () -> l)

  let make_iite {r_iite_h} a b c =
    let (i : iite) = a, b, c in
    Hashtbl.find_or_add r_iite_h i ~default:(fun () -> B_Ite i)

  let rec negate = function
    | U_Not U_Not g ->
      negate g
    | U_Not g ->
      g
    | g ->
      U_Not g

  let rec elim_not_not = function
    | U_Not U_Not g ->
      elim_not_not g
    | g ->
      g

  let rec compare_formula_abs x y =
    match x, y with
    | U_Not U_Not x, _ ->
      compare_formula_abs (elim_not_not x) y
    | _, U_Not U_Not y ->
      compare_formula_abs x (elim_not_not y)
    | U_Not x, U_Not y ->
      compare_formula x y
    | U_Not x, y ->
      let i = compare_formula x y in
      if i = 0 then -1 else i
    | x, U_Not y ->
      let i = compare_formula x y in
      if i = 0 then 1 else i
    | _, _ ->
      compare_formula x y

  let rec flatten_args :
  type s t . ctx -> ibflat list -> (I.c, s -> t) M.t -> app =
    fun r acc -> function
    | M.M_App (f, t) ->
      flatten_args r (flatten_term r t :: acc) f
    | M.M_Var v ->
      Lang_ids.Box_arrow.Box v, make_args r (List.rev acc)

  and flatten_int_term_aux r (d, x) k (t : (_, int) M.t) =
    match t with
    | M.M_Var v ->
      (k, B_Var v) :: d, x
    | M.M_Int i ->
      d, Int63.(x + k * i)
    | M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
      (k, B_App a) :: d, x
    | M.M_Sum (s, t) ->
      let d, x = flatten_int_term_aux r (d, x) k s in
      flatten_int_term_aux r (d, x) k t
    | M.M_Prod (k2, t) ->
      flatten_int_term_aux r (d, x) Int63.(k * k2) t
    | M.M_Ite (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_int_term r s
      and t = flatten_int_term r t in
      (k, make_iite r c s t) :: d, x

  and flatten_int_term ({r_sum_h} as r) = function
    | M.M_Var v ->
      G_Base (B_Var v)
    | M.M_Ite (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_int_term r s
      and t = flatten_int_term r t in
      G_Base (make_iite r c s t)
    | M.M_App (f, t) ->
      G_Base (B_App (flatten_args r [flatten_term r t] f))
    | M.M_Int _ | M.M_Sum (_, _) | M.M_Prod (_, _) as t ->
      let d, x = [], Int63.zero in
      let d, x = flatten_int_term_aux r (d, x) Int63.one t in
      G_Sum (make_sum r d x)

  and flatten_bool_term r = function
    | M.M_Var v ->
      U_Var v
    | M.M_Bool g ->
      flatten_formula r g
    | M.M_App (f, t)  ->
      let l = flatten_args r [flatten_term r t] f in
      U_App l

  and flatten_term :
  type s . ctx -> (I.c, s) M.t -> ibflat =
    fun r t ->
      match M.type_of_t t ~f:I.type_of_t' with
      | Lang_types.Y_Int ->
        H_Int (flatten_int_term r t)
      | Lang_types.Y_Bool ->
        H_Bool (flatten_bool_term r t)
      | _ ->
        (* not meant for functions *)
        raise (Unreachable.Exn _here_)
          
  and flatten_formula_aux r d = function
    | Formula.F_True ->
      d
    | Formula.F_And (g, h) ->
      let d = flatten_formula_aux r d g in
      flatten_formula_aux r d h
    | g ->
      flatten_formula r g :: d
        
  and flatten_formula r = function
    | Formula.F_True ->
      U_And []
    | Formula.F_Atom (A.A_Bool t) ->
      flatten_bool_term r t
    | Formula.F_Atom (A.A_Le t) ->
      U_Atom (flatten_int_term r t, O'_Le)
    | Formula.F_Atom (A.A_Eq t) ->
      U_Atom (flatten_int_term r t, O'_Eq)
    | Formula.F_Not g ->
      negate (flatten_formula r g)
    | Formula.F_Ite (q, g, h) ->
      U_Ite (flatten_formula r q,
             flatten_formula r g,
             flatten_formula r h)
    | Formula.F_And (_, _) as g ->
      U_And (flatten_formula_aux r [] g)

end
