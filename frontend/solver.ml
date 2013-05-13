open Core.Std
open Terminology

exception Unreachable_Exn of Here.t

module Make (S : Imt_intf.S) (I : Lang_ids.Accessors) = struct

  module P = Pre.Make(I)

  module LA = Lang_abstract

  type c = I.c

  type 't term = (I.c, 't) LA.M.t

  type formula = I.c LA.A.t Formula.t

  type fun_id = F_Id : (I.c, 's -> 't) Lang_ids.t -> fun_id

  type int_id  = (I.c, int) Lang_ids.t
  
  type bool_id = (I.c, bool) Lang_ids.t

  let type_of_term :
  type t . t term -> t Lang_types.t =
    fun x -> Lang_abstract.M.type_of_t ~f:I.type_of_t' x

  (* flat internal representation of terms and formulas *)

  type ibflat = (flat_term, flat_formula) ibeither
    
  and flat_app = fun_id * ibflat list

  and flat_sum = (Int63.t * flat_term_base) list

  and flat_term_base =
    B_Var   of  S.ivar
  | B_App   of  flat_app
  | B_Ite   of  flat_formula * flat_term * flat_term

  and flat_term =
    G_Base  of  flat_term_base
  | G_Sum   of  flat_sum offset

  and flat_formula =
    U_Var   of  S.bvar
  | U_Atom  of  flat_term * op'
  | U_Not   of  flat_formula
  | U_And   of  flat_formula list
  | U_App   of  flat_app
  | U_Ite   of  flat_formula * flat_formula * flat_formula

  (* operators *)

  (* we will expand-out ITE right before blasting *)
  let ff_ite q g h =
    let ff_not = function U_Not g -> g | g -> U_Not g in
    let ff_or a b = U_Not (U_And [ff_not a; ff_not b]) in
    U_And [ff_or (ff_not q) g; ff_or q h]

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
    r_xvar_m           :  (flat_formula, xvar) Hashtbl.Poly.t;
    r_fun_m            :  (fun_id, S.f) Hashtbl.Poly.t;
    r_call_m           :  (S.f * ovar list, S.ivar) Hashtbl.Poly.t;
    r_ivar_m           :  (int_id, S.ivar) Hashtbl.Poly.t;
    r_bvar_m           :  (bool_id, S.bvar) Hashtbl.Poly.t;
    r_q                :  flat_formula Dequeue.t;
    mutable r_fun_cnt  :  int;
    mutable r_unsat    :  bool
  }

  let make_ctx () = {
    r_ctx     = S.new_ctx ();
    r_xvar_m  = Hashtbl.Poly.create ~size:10240 ();
    r_fun_m   = Hashtbl.Poly.create ~size:512 ();
    r_call_m  = Hashtbl.Poly.create ~size:2048 ();
    r_ivar_m  = Hashtbl.Poly.create ~size:10240 ();
    r_bvar_m  = Hashtbl.Poly.create ~size:10240 ();
    r_q       = Dequeue.create () ~dummy:(U_And []);
    r_fun_cnt = 0;
    r_unsat   = false
  }

  let get_f ({r_ctx; r_fun_m; r_fun_cnt} as r) (F_Id id' as id) =
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

  (* flatten terms and formulas; SCC impractical to break *)

  let rec flatten_args :
  type s t . ctx -> ibflat list -> (s -> t) term -> flat_app =
    fun r acc -> function
    | LA.M.M_App (f, t) ->
      flatten_args r (flatten_term r t :: acc) f
    | LA.M.M_Var v ->
      F_Id v, List.rev acc

  and flatten_int_term_aux r (d, x) k (t : int term) =
    match t with
    | LA.M.M_Var v ->
      (k, B_Var (get_int_var r v)) :: d, x
    | LA.M.M_Int i ->
      d, Int63.(x + k * i)
    | LA.M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
      (k, B_App a) :: d, x
    | LA.M.M_Sum (s, t) ->
      let d, x = flatten_int_term_aux r (d, x) k s in
      flatten_int_term_aux r (d, x) k t
    | LA.M.M_Prod (k2, t) ->
      flatten_int_term_aux r (d, x) Int63.(k * k2) t
    | LA.M.M_Ite (c, s, t) ->
      (k, B_Ite (flatten_formula r c,
                 flatten_int_term r s,
                 flatten_int_term r t)) :: d, x

  and flatten_int_term r = function
    | LA.M.M_Var v ->
      G_Base (B_Var (get_int_var r v))
    | LA.M.M_Ite (c, s, t) ->
      G_Base
        (B_Ite (flatten_formula r c,
                flatten_int_term r s,
                flatten_int_term r t))
    | LA.M.M_App (f, t) ->
      G_Base (B_App (flatten_args r [flatten_term r t] f))
    | LA.M.M_Int _ | LA.M.M_Sum (_, _) | LA.M.M_Prod (_, _) as t ->
      let d, x = [], Int63.zero in
      let d, x = flatten_int_term_aux r (d, x) Int63.one t in
      (* dedup / sort / hash here *)
      G_Sum (d, x)

  and flatten_bool_term r = function
    | LA.M.M_Var v ->
      U_Var (get_bool_var r v)
    | LA.M.M_Bool g ->
      flatten_formula r g
    | LA.M.M_App (f, t)  ->
      let l = flatten_args r [flatten_term r t] f in
      U_App l

  and flatten_term :
  type t . ctx -> t term -> ibflat =  
    fun r t ->
      match type_of_term t with
      | Lang_types.Y_Int ->
        H_Int (flatten_int_term r t)
      | Lang_types.Y_Bool ->
        H_Bool (flatten_bool_term r t)
      | _ ->
        (* not meant for functions *)
        raise (Unreachable_Exn _here_)
        
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
    | Formula.F_Atom (LA.A.A_Bool t) ->
      flatten_bool_term r t
    | Formula.F_Atom (LA.A.A_Le t) ->
      U_Atom (flatten_int_term r t, O'_Le)
    | Formula.F_Atom (LA.A.A_Eq t) ->
      U_Atom (flatten_int_term r t, O'_Eq)
    | Formula.F_Not g ->
      U_Not (flatten_formula r g)
    | Formula.F_Ite (q, g, h) ->
      U_Ite (flatten_formula r q,
             flatten_formula r g,
             flatten_formula r h)
    | Formula.F_And (_, _) as g ->
      U_And (flatten_formula_aux r [] g)

  (* linearizing terms and formulas: utilities before we get into the
     mutually recursive part *)

  let snot = function
    | S_Pos x -> S_Neg x
    | S_Neg x -> S_Pos x

  let negate_isum =
    List.map ~f:(Tuple.T2.map1 ~f:Int63.neg)

  (* linearizing terms and formulas: mutual recursion, because terms
     contain formulas and vice versa *)

  let rec iexpr_of_sum r l o =
    let f (l, o) (c, t) =
      match ovar_of_flat_term_base r t with
      | Some v, x ->
        (c, v) :: l, Int63.(o + c * x)
      | None, x ->
        l, Int63.(o + c * x)
    and init = [], o in
    List.fold_left ~init ~f l

  and blast_le ?v ({r_ctx} as r) s o =
    let ((s, o) as ie) = iexpr_of_sum r s o
    and v = match v with Some v -> v | _ -> S.new_bvar r_ctx in
    S.add_indicator r_ctx (S_Pos v) ie;
    let neg_sum = negate_isum s in
    S.add_indicator r_ctx (S_Neg v) (neg_sum, Int63.(one - o));
    S_Pos (Some v)

  and blast_eq ({r_ctx} as r) s o =
    let ((s, o) as ie) = iexpr_of_sum r s o in
    let neg_sum = negate_isum s in
    let v = S.new_bvar r_ctx in
    let vp_lt = S_Pos (S.new_bvar r_ctx)
    and vp_gt = S_Pos (S.new_bvar r_ctx)
    and vp = S_Pos v in
    S.add_indicator r_ctx vp ie;
    S.add_indicator r_ctx vp (neg_sum, Int63.neg o);
    S.add_indicator r_ctx vp_lt (s, Int63.(o + one));
    S.add_indicator r_ctx vp_gt (neg_sum, Int63.(one - o));
    S.add_clause r_ctx [vp; vp_lt; vp_gt];
    S_Pos (Some v)

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
      | G_Sum (l, o) ->
        iexpr_of_sum r l o
      | G_Base b ->
        (match ovar_of_flat_term_base r b with
        | Some v, x ->
          [Int63.one, v], x
        | None, x ->
          [], x) in
    let l, o as ie = (Int63.minus_one, v) :: l, o in
    S.add_indicator r_ctx xv ie;
    let l, o as ie = negate_isum l, Int63.neg o in
    S.add_indicator r_ctx xv ie

  and ovar_of_ite ({r_ctx} as r) g s t =
    match xvar_of_formula r g with
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
    | S_Pos None ->
      ovar_of_term r s
    | S_Neg None ->
      ovar_of_term r t

  and ovar_of_flat_term_base ({r_ctx} as r) = function
    | B_Var v ->
      Some v, Int63.zero
    | B_App (f_id, l) ->
      Some (var_of_app r f_id l mip_type_int), Int63.zero
    | B_Ite (g, s, t) ->
      ovar_of_ite r g s t

  and ovar_of_term ({r_ctx} as r) = function
    | G_Base b ->
      ovar_of_flat_term_base r b
    | G_Sum (l, o) ->
      (match iexpr_of_sum r l o with
      | [], o ->
        None, o
      | [c, x], o when c = Int63.one ->
        Some x, o
      | l, o ->
        let v = S.new_ivar r_ctx mip_type_int in
        S.add_eq r_ctx ((Int63.minus_one, v) :: l, o);
        Some v, Int63.zero)

  and ovar_of_ibeither ({r_ctx} as r) = function
    | H_Int (G_Base b) ->
      ovar_of_flat_term_base r b
    | H_Int (G_Sum (l, o)) ->
      (match iexpr_of_sum r l o with
      | [], o ->
        None, o
      | [c, x], o when c = Int63.one ->
        Some x, o
      | l, o ->
        let v = S.new_ivar r_ctx mip_type_int in
        S.add_eq r_ctx ((Int63.minus_one, v) :: l, o);
        Some v, Int63.zero)
    | H_Bool g ->
      (match xvar_of_formula r g with
      | S_Pos (Some v) ->
        Some (S.ivar_of_bvar v), Int63.zero
      | S_Neg (Some v) ->
        Some (S.ivar_of_bvar (S.negate_bvar r_ctx v)), Int63.zero
      | S_Pos None ->
        None, Int63.one
      | S_Neg None ->
        None, Int63.zero)

  and blast_atom ({r_ctx} as r) = function
    | G_Base t, O'_Le ->
      blast_le r [Int63.one, t] Int63.zero
    | G_Sum (s, o), O'_Le ->
      blast_le r s o
    | G_Base t, O'_Eq ->
      blast_eq r [Int63.one, t] Int63.zero
    | G_Sum (s, o), O'_Eq ->
      blast_eq r s o

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

  and blast_formula ({r_ctx} as r) = function
    | U_Var v ->
      S_Pos (Some v)
    | U_App (f_id, l) ->
      S_Pos (Some (S.bvar_of_ivar
                     (var_of_app r f_id l mip_type_bool)))
    | U_Atom (t, o) ->
      blast_atom r (t, o)
    | U_Not g ->
      snot (blast_formula r g)
    | U_And l ->
      blast_conjunction r l
    | U_Ite (q, g, h) ->
      blast_formula r (ff_ite q g h)

  and xvar_of_formula ({r_xvar_m} as r) g =
    let default () = blast_formula r g in
    Hashtbl.find_or_add r_xvar_m g ~default

  let finally_assert_unit ({r_ctx} as r) = function
    | S_Pos (Some v) ->
      let v = S.ivar_of_bvar v in
      S.add_eq r_ctx ([Int63.one, v], Int63.minus_one)
    | S_Neg (Some v) ->
      let v = S.ivar_of_bvar v in
      S.add_eq r_ctx ([Int63.one, v], Int63.zero)
    | S_Pos None ->
      ()
    | S_Neg None ->
      r.r_unsat <- true

  let rec finally_assert_formula r = function
    | U_And l ->
      List.iter l ~f:(finally_assert_formula r)
    | g ->
      finally_assert_unit r (xvar_of_formula r g)

  let assert_formula ({r_q} as r) g =
    Dequeue.push_back r_q (flatten_formula r g)

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
