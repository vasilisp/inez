open Core.Std
open Terminology

module Make_compiler

  (S : Imt_intf.S_access) (I : Lang_ids.Accessors) =

struct

  open Lang_abstract

  module P = Pre.Make(I)

  type c = I.c

  type 't term = (I.c, 't) M.t

  type formula = I.c A.t Formula.t

  type fun_id = I.c Lang_ids.Box_arrow.t
  with sexp_of, compare

  type int_id  = (I.c, int) Lang_ids.t
  with sexp_of, compare
  
  type bool_id = (I.c, bool) Lang_ids.t
  with sexp_of, compare

  let hashable_fun_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_fun_id;
    sexp_of_t = sexp_of_fun_id
  }

  let hashable_int_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_int_id;
    sexp_of_t = sexp_of_int_id
  }

  let hashable_bool_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bool_id;
    sexp_of_t = sexp_of_bool_id
  }

  let type_of_term :
  type t . t term -> t Lang_types.t =
    fun x -> M.type_of_t ~f:I.type_of_t' x

  let flat_sum_negate (l, x) =
    List.map l ~f:(Tuple.T2.map1 ~f:Int63.neg), Int63.neg x

  type ovar = S.ivar option offset

  (* optional var, possibly negated (S_Pos None means true) *)

  type xvar = S.bvar option signed

  let xtrue = S_Pos None

  let xfalse = S_Neg None

  (* standard MIP types *)

  let mip_type_int = T_Int (None, None)

  let mip_type_bool = T_Int (Some Int63.zero, Some Int63.one)

  (* context *)

  type ctx = {
    r_ctx              :  S.ctx;
    r_pre_ctx          :  P.ctx;
    r_xvar_m           :  (P.formula, xvar) Hashtbl.t;
    r_fun_m            :  (fun_id, S.f) Hashtbl.t;
    r_call_m           :  (S.f * ovar list, S.ivar) Hashtbl.t;
    r_ivar_m           :  (int_id, S.ivar) Hashtbl.t;
    r_bvar_m           :  (bool_id, S.bvar) Hashtbl.t;
    r_q                :  P.formula Dequeue.t;
    mutable r_fun_cnt  :  int;
    mutable r_unsat    :  bool
  }

  let get_f ({r_ctx; r_fun_m; r_fun_cnt} as r)
      (Lang_ids.Box_arrow.Box id' as id) =
    let t = I.type_of_t id' in
    Hashtbl.find_or_add r_fun_m id
      ~default:(fun () ->
        let s = Printf.sprintf "f_%d" r_fun_cnt in
        r.r_fun_cnt <- r.r_fun_cnt + 1;
        S.new_f r_ctx s (Lang_types.count_arrows t))

  let get_int_var {r_ctx; r_ivar_m} (x : int_id) =
    Hashtbl.find_or_add r_ivar_m x
      ~default:(fun () -> S.new_ivar r_ctx mip_type_int)

  let get_bool_var {r_ctx; r_bvar_m} (x : bool_id) =
    Hashtbl.find_or_add r_bvar_m x
      ~default:(fun () -> S.new_bvar r_ctx)

  (* linearizing terms and formulas: utilities before we get into the
     mutually recursive part *)

  let snot = function
    | S_Pos x -> S_Neg x
    | S_Neg x -> S_Pos x

  let negate_isum =
    List.map ~f:(Tuple.T2.map1 ~f:Int63.neg)

  (* linearizing terms and formulas: mutual recursion, because terms
     contain formulas and vice versa *)

  let rec iexpr_of_sum r (l, o) =
    let f (l, o) (c, t) =
      match ovar_of_flat_term_base r t with
      | Some v, x ->
        (c, v) :: l, Int63.(o + c * x)
      | None, x ->
        l, Int63.(o + c * x)
    and init = [], o in
    List.fold_left ~init ~f l

  and blast_le ?v ({r_ctx} as r) s =
    let l, o = iexpr_of_sum r s
    and v = match v with Some v -> v | _ -> S.new_bvar r_ctx in
    S.add_indicator r_ctx (S_Pos v)  l                (Int63.neg o);
    S.add_indicator r_ctx (S_Neg v)  (negate_isum l)  Int63.(o - one);
    S_Pos (Some v)

  and blast_eq ({r_ctx} as r) s =
    let l, o = iexpr_of_sum r s in
    let l_neg = negate_isum l in
    let b    = S.new_bvar r_ctx in
    let b_lt = S_Pos (S.new_bvar r_ctx)
    and b_gt = S_Pos (S.new_bvar r_ctx)
    and b_eq = S_Pos b in
    S.add_indicator r_ctx b_eq  l      (Int63.neg o);
    S.add_indicator r_ctx b_eq  l_neg  o;
    S.add_indicator r_ctx b_lt  l      Int63.(neg o - one);
    S.add_indicator r_ctx b_gt  l_neg  Int63.(o - one);
    S.add_clause r_ctx [b_eq; b_lt; b_gt];
    S_Pos (Some b)

  and var_of_app ({r_ctx; r_call_m} as r) f_id l t =
    let f = get_f r f_id
    and l = List.map l ~f:(ovar_of_ibeither r)
    and default () = S.new_ivar r_ctx t in
    let v = Hashtbl.find_or_add r_call_m (f, l) ~default in
    S.add_call r_ctx (Some v, Int63.zero) f l;
    v

  and blast_ite_branch ({r_ctx} as r) xv v e =
    let l, o =
      match e with
      | P.G_Sum s ->
        iexpr_of_sum r s
      | P.G_Base b ->
        (match ovar_of_flat_term_base r b with
        | Some v, x ->
          [Int63.one, v], x
        | None, x ->
          [], x) in
    let l = (Int63.minus_one, v) :: l in
    S.add_indicator r_ctx xv  l                (Int63.neg o);
    S.add_indicator r_ctx xv  (negate_isum l)  o

  and ovar_of_ite ({r_ctx} as r) g s t =
    match xvar_of_formula r g with
    | S_Pos None ->
      ovar_of_term r s
    | S_Neg None ->
      ovar_of_term r t
    | S_Pos (Some bv) ->
      let v = S.new_ivar r_ctx mip_type_int in
      blast_ite_branch r (S_Pos bv) v s;
      blast_ite_branch r (S_Neg bv) v t;
      Some v, Int63.zero
    | S_Neg (Some bv) ->
      let v = S.new_ivar r_ctx mip_type_int in
      blast_ite_branch r (S_Neg bv) v s;
      blast_ite_branch r (S_Pos bv) v t;
      Some v, Int63.zero

  and ovar_of_flat_term_base r = function
    | P.B_Var v ->
      Some (get_int_var r v), Int63.zero
    | P.B_Formula g ->
      ovar_of_formula r g
    | P.B_App (f_id, l) ->
      Some (var_of_app r f_id l mip_type_int), Int63.zero
    | P.B_Ite (g, s, t) ->
      ovar_of_ite r g s t

  and ovar_of_term ({r_ctx} as r) = function
    | P.G_Base b ->
      ovar_of_flat_term_base r b
    | P.G_Sum s ->
      (match iexpr_of_sum r s with
      | [], o ->
        None, o
      | [c, x], o when c = Int63.one ->
        Some x, o
      | l, o ->
        let v = S.new_ivar r_ctx mip_type_int in
        S.add_eq r_ctx ((Int63.minus_one, v) :: l) (Int63.neg o);
        Some v, Int63.zero)

  and ovar_of_formula ({r_ctx} as r) g =
    match xvar_of_formula r g with
    | S_Pos (Some v) ->
      Some (S.ivar_of_bvar v), Int63.zero
    | S_Neg (Some v) ->
      Some (S.ivar_of_bvar (S.negate_bvar r_ctx v)), Int63.zero
    | S_Pos None ->
      None, Int63.one
    | S_Neg None ->
      None, Int63.zero

  and ovar_of_ibeither ({r_ctx} as r) = function
    | H_Int (P.G_Base b) ->
      ovar_of_flat_term_base r b
    | H_Int (P.G_Sum s) ->
      (match iexpr_of_sum r s with
      | [], o ->
        None, o
      | [c, x], o when c = Int63.one ->
        Some x, o
      | l, o ->
        let v = S.new_ivar r_ctx mip_type_int in
        S.add_eq r_ctx ((Int63.minus_one, v) :: l) (Int63.neg o);
        Some v, Int63.zero)
    | H_Bool g ->
      ovar_of_formula r g

  and blast_atom ({r_ctx} as r) = function
    | P.G_Base t, O'_Le ->
      blast_le r ([Int63.one, t], Int63.zero)
    | P.G_Sum s, O'_Le ->
      blast_le r s
    | P.G_Base t, O'_Eq ->
      blast_eq r ([Int63.one, t], Int63.zero)
    | P.G_Sum s, O'_Eq ->
      blast_eq r s

  and blast_conjunction_map r acc = function
    | g :: tail ->
      (match blast_formula r g with
      | S_Pos (Some x) ->
        blast_conjunction_map r (S_Pos x :: acc) tail
      | S_Pos None ->
        blast_conjunction_map r acc tail
      | S_Neg (Some x) ->
        blast_conjunction_map r (S_Neg x :: acc) tail
      | S_Neg None ->
        None)
    | [] ->
      Some acc

  and blast_conjunction_reduce {r_ctx} l =
    match l with
    | [] ->
      xtrue
    | [S_Pos x] ->
      S_Pos (Some x)
    | [S_Neg x] ->
      S_Neg (Some x)
    | _ ->
      let rval = S.new_bvar r_ctx in
      (let f v = S.add_clause r_ctx [S_Neg rval; v] in
       List.iter l ~f);
      S.add_clause r_ctx (S_Pos rval :: List.map l ~f:snot);
      S_Pos (Some rval)

  and blast_conjunction r l =
    Option.value_map (blast_conjunction_map r [] l)
      ~f:(blast_conjunction_reduce r)
      ~default:xfalse

  and blast_formula r = function
    | P.U_Var v ->
      S_Pos (Some (get_bool_var r v))
    | P.U_App (f_id, l) ->
      S_Pos (Some (S.bvar_of_ivar
                     (var_of_app r f_id l mip_type_bool)))
    | P.U_Atom (t, o) ->
      blast_atom r (t, o)
    | P.U_Not g ->
      snot (blast_formula r g)
    | P.U_And l ->
      blast_conjunction r l
    | P.U_Ite (q, g, h) ->
      blast_formula r (P.ff_ite q g h)

  and xvar_of_formula ({r_xvar_m} as r) g =
    let default () = blast_formula r g in
    Hashtbl.find_or_add r_xvar_m g ~default

  let assert_ivar_equal_constant {r_ctx} v c =
    S.add_eq r_ctx [Int63.one, v] c

  let assert_ivar_le_constant {r_ctx} v c =
    S.add_le r_ctx [Int63.one, v] c

  let assert_bvar_equal_constant {r_ctx} v c =
    let v = S.ivar_of_bvar v in
    S.add_eq r_ctx [Int63.one, v] c

  let finally_assert_unit ({r_ctx} as r) = function
    | S_Pos (Some v) ->
      assert_bvar_equal_constant r v Int63.one
    | S_Neg (Some v) ->
      assert_bvar_equal_constant r v Int63.zero
    | S_Pos None ->
      ()
    | S_Neg None ->
      r.r_unsat <- true

  let rec finally_assert_formula ({r_ctx} as r) = function
    | P.U_And l ->
      List.iter l ~f:(finally_assert_formula r)
    | P.U_Var v ->
      assert_bvar_equal_constant r (get_bool_var r v) Int63.one
    | P.U_App (f_id, l) ->
      let v = var_of_app r f_id l mip_type_bool in
      assert_ivar_equal_constant r v Int63.one
    | P.U_Atom (P.G_Sum s, O'_Le) ->
      let l, o = iexpr_of_sum r s in
      S.add_le r_ctx l (Int63.neg o)
    | P.U_Atom (P.G_Sum s, O'_Eq) ->
      let l, o = iexpr_of_sum r s in
      S.add_eq r_ctx l (Int63.neg o)
    | P.U_Atom (P.G_Base a, O'_Le) ->
      (match ovar_of_flat_term_base r a with
      | None, o when Int63.(o > zero) ->
        r.r_unsat <- true
      | None, _ ->
        ()
      | Some v, o ->
        assert_ivar_le_constant r v (Int63.neg o))
    | P.U_Atom (P.G_Base a, O'_Eq) ->
      (match ovar_of_flat_term_base r a with
      | None, o when Int63.(o = zero) ->
        ()
      | None, _ ->
        r.r_unsat <- true
      | Some v, o ->
        assert_ivar_equal_constant r v (Int63.neg o))
    | g ->
      finally_assert_unit r (xvar_of_formula r g)

  let assert_formula {r_pre_ctx; r_q} g =
    Dequeue.push_back r_q (P.flatten_formula r_pre_ctx g)

  let write_bg_ctx {r_ctx} =
    S.write_ctx r_ctx

  let solve ({r_q; r_ctx} as r) =
    Dequeue.iter r_q ~f:(finally_assert_formula r);
    Dequeue.clear r_q;
    if r.r_unsat then
      R_Unsat
    else
      S.solve r_ctx

  let deref_int {r_ctx; r_ivar_m} id =
    match Hashtbl.find r_ivar_m id with
    | Some v ->
      S.ideref r_ctx v
    | None ->
      None

  let deref_bool {r_ctx; r_bvar_m} id =
    match Hashtbl.find r_bvar_m id with
    | Some v ->
      S.bderef r_ctx v
    | None ->
      None

end

module Make (S : Imt_intf.S) (I : Lang_ids.Accessors) = struct

  include Make_compiler(S)(I)

  let make_ctx () = {
    r_ctx     = S.new_ctx ();
    r_pre_ctx = P.make_ctx ();
    r_xvar_m  =
      Hashtbl.create () ~size:10240 ~hashable:P.hashable_formula;
    r_fun_m   =
      Hashtbl.create () ~size:512 ~hashable:hashable_fun_id;
    r_call_m  =
      Hashtbl.Poly.create ~size:2048 ();
    r_ivar_m  =
      Hashtbl.create () ~size:10240 ~hashable:hashable_int_id;
    r_bvar_m  =
      Hashtbl.create () ~size:10240 ~hashable:hashable_bool_id;
    r_q       = Dequeue.create () ~dummy:P.dummy_formula;
    r_fun_cnt = 0;
    r_unsat   = false
  }

end

(* TODO : implement a variant of Make that also accepts a DP
   module. *)
