open Core.Std
open Terminology

module Make (S : Imt_intf.S) (I : sig type c end) = struct

  module LA = Lang_abstract

  (* TODO: use herelib for inserting locations *)
  exception Exn_unreachable of string

  type c = I.c

  type 't term = (c, 't) LA.term

  type ibterm = C_Bool of bool term | C_Int of int term

  type formula = c LA.atom Formula.formula

  type fun_id =
    F_Id :
      (c, 's -> 't) Lang_ids.t * ('s -> 't) Lang_types.t -> fun_id

  type int_id = (c, int) Lang_ids.t

  type bool_id = (c, bool) Lang_ids.t

  (* flat internal representation of terms and formulas *)

  type flat_term_sum = (Int63.t * flat_term_base) list

  and flat_term =
    L_Base  of  flat_term_base
  | L_Sum   of  flat_term_sum offset
  | L_Bool  of  flat_formula

  (* trying to restrict what can appear where *)

  and flat_term_base =
    B_Var   of  S.var
  | B_App   of  flat_app
  | B_Ite   of  flat_formula * flat_term * flat_term

  (* flat_term without the bool case, for use as an atomic formula *)
  and flat_term_atom =
    G_Base  of  flat_term_base
  | G_Sum   of  flat_term_sum offset

  and flat_formula =
    U_Var   of  S.var
  | U_Atom  of  flat_term_atom * op'
  | U_Not   of  flat_formula
  | U_And   of  flat_formula list
  | U_App   of  flat_app
  | U_Ite   of  flat_formula * flat_formula * flat_formula

  and flat_app = fun_id * flat_term list

  (* we will expand-out ITE right before blasting *)

  let ff_ite q g h =
    let ff_not = function U_Not g -> g | g -> U_Not g in
    let ff_or a b = U_Not (U_And [ff_not a; ff_not b]) in
    U_And [ff_or (ff_not q) g; ff_or q h]

  type ovar = S.var option offset

  (* optional var, possibly negated (S_Pos None means true) *)

  type xvar = S.var option signed

  let xtrue = S_Pos None

  let xfalse = S_Neg None

  (* standard MIP types *)

  let mip_type_bool =
    T_Int (Some Int63.zero, Some Int63.one)

  let mip_type_int =
    T_Int (None, None)

  (* context *)

  type ctx = {
    r_ctx              :  S.ctx;
    r_xvar_m           :  (flat_formula, xvar) Hashtbl.Poly.t;
    r_fun_m            :  (fun_id, S.f) Hashtbl.Poly.t;
    r_call_m           :  (S.f * ovar list, S.var) Hashtbl.Poly.t;
    r_ivar_m           :  (int_id, S.var) Hashtbl.Poly.t;
    r_bvar_m           :  (bool_id, S.var) Hashtbl.Poly.t;
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

  let get_f ({r_ctx; r_fun_m; r_fun_cnt} as r)
      (F_Id (_, t) as id) =
    Hashtbl.find_or_add r_fun_m id
      ~default:(fun () ->
        let s = Printf.sprintf "f_%d" r_fun_cnt in
        r.r_fun_cnt <- r.r_fun_cnt + 1;
        S.new_f r_ctx s (Lang_types.count_arrows t))

  let get_int_var {r_ctx; r_ivar_m} (x : int_id) =
    Hashtbl.find_or_add r_ivar_m x
      ~default:(fun () -> S.new_var r_ctx mip_type_int)

  let get_bool_var {r_ctx; r_bvar_m} (x : bool_id) =
    Hashtbl.find_or_add r_bvar_m x
      ~default:(fun () -> S.new_var r_ctx mip_type_int)

  (* flatten terms and formulas; SCC impractical to break *)

  let rec flatten_args :
  type s t .
  ctx -> flat_term list -> (s -> t) term -> flat_app =
    fun r acc -> function
    | LA.M_App (f, t) ->
      flatten_args r (flatten_term r t :: acc) f
    | LA.M_Var (i, t) ->
      F_Id (i, t), List.rev acc
    | _ ->
      raise (Exn_unreachable "GADTs confuse exhaustiveness checker")

  and flatten_int_term_aux r (d, x) k (t : int term) =
    match t with
    | LA.M_Var (v, _) ->
      (k, B_Var (get_int_var r v)) :: d, x
    | LA.M_Int i ->
      d, Int63.(x + k * i)
    | LA.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
      (k, B_App a) :: d, x
    | LA.M_Sum (s, t) ->
      let d, x = flatten_int_term_aux r (d, x) k s in
      flatten_int_term_aux r (d, x) k t
    | LA.M_Prod (k2, t) ->
      flatten_int_term_aux r (d, x) Int63.(k * k2) t
    | LA.M_Ite (c, s, t) ->
      (k, B_Ite (flatten_formula r c,
                 flatten_term r s,
                 flatten_term r t)) :: d, x

  and flatten_int_term r (t : int term) =
    let d, x = [], Int63.zero in
    let d, x = flatten_int_term_aux r (d, x) Int63.one t in
    (* dedup / sort / hash d here *)
    L_Sum (d, x)

  and flatten_term :
  type t . ctx -> t term -> flat_term =
    fun r -> function
    | LA.M_Var (v, Lang_types.Y_Int) ->
      L_Base (B_Var (get_int_var r v))
    | LA.M_Var (v, Lang_types.Y_Bool) ->
      L_Bool (U_Var (get_bool_var r v))
    | LA.M_Var (_, _) ->
      raise (Exn_unreachable "not meant for functions")
    | LA.M_Ite (c, s, t) ->
      L_Base
        (B_Ite (flatten_formula r c,
                flatten_term r s,
                flatten_term r t))
    | LA.M_App (f, t) ->
      L_Base (B_App (flatten_args r [flatten_term r t] f))
    | LA.M_Bool g ->
      L_Bool (flatten_formula r g)
    (* flatten_int_term for remaining int cases *)
    | LA.M_Int _ as t ->
      flatten_int_term r t
    | LA.M_Sum (_, _) as t ->
      flatten_int_term r t
    | LA.M_Prod (_, _) as t ->
      flatten_int_term r t

  and flatten_bool_term r (t : bool term) =
    match t with
    | LA.M_Var (v, Lang_types.Y_Bool) ->
      U_Var (get_bool_var r v)
    | LA.M_Bool g ->
      flatten_formula r g
    | LA.M_App (f, t)  ->
      let l = flatten_args r [flatten_term r t] f in
      U_App l
    | _ ->
      raise (Exn_unreachable "GADTs confuse exhaustiveness checker")

  and flatten_term_for_atom r t =
    match flatten_term r t with
    | L_Base b -> G_Base b
    | L_Sum s -> G_Sum s
    | L_Bool _ -> raise (Exn_unreachable "invalid casting")

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
    | Formula.F_Atom (LA.A_Bool t) ->
      flatten_bool_term r t
    | Formula.F_Atom (LA.A_Le t) ->
      U_Atom (flatten_term_for_atom r t, O'_Le)
    | Formula.F_Atom (LA.A_Eq t) ->
      U_Atom (flatten_term_for_atom r t, O'_Eq)
    | Formula.F_Not g ->
      U_Not (flatten_formula r g)
    | Formula.F_Ite (q, g, h) ->
      U_Ite (flatten_formula r q,
             flatten_formula r g,
             flatten_formula r h)
    | Formula.F_And (_, _) as g ->
      U_And (flatten_formula_aux r [] g)

  (* flatten terms *)

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

  and blast_le ({r_ctx} as r) s o =
    let ie = iexpr_of_sum r s o
    and v = S.new_var r_ctx mip_type_bool in
    S.add_indicator r_ctx (S_Pos v) ie;
    S_Pos (Some v)

  and blast_eq ({r_ctx} as r) s o =
    let ((s, o) as ie) = iexpr_of_sum r s o in
    let neg_sum = negate_isum s in
    let v = S.new_var r_ctx mip_type_bool in
    let vp_lt = S_Pos (S.new_var r_ctx mip_type_bool)
    and vp_gt = S_Pos (S.new_var r_ctx mip_type_bool)
    and vp = S_Pos v in
    S.add_indicator r_ctx vp ie;
    S.add_indicator r_ctx vp (neg_sum, Int63.neg o);
    S.add_indicator r_ctx vp_lt (s, Int63.(o + one));
    S.add_indicator r_ctx vp_gt (neg_sum, Int63.(one - o));
    S.add_clause r_ctx [vp; vp_lt; vp_gt];
    S_Pos (Some v)

  and var_of_app ({r_ctx; r_call_m} as r) f_id l t =
    let f = get_f r f_id
    and l = List.map l ~f:(ovar_of_flat_term r)
    and default () = S.new_var r_ctx t in
    let v = Hashtbl.find_or_add r_call_m (f, l) ~default in
    S.add_call r_ctx (Some v, Int63.zero) f l;
    v

  and ovar_of_flat_term_base ({r_ctx} as r) = function
    | B_Var v ->
      Some v, Int63.zero
    | B_App (f_id, l) ->
      Some (var_of_app r f_id l mip_type_int), Int63.zero
    | B_Ite (g, s, t) ->
      (* FIXME *)
      None, Int63.zero

  (* hash calls; temporary solution, till we implement more general
     hashing and sharing *)

  and ovar_of_flat_term ({r_ctx} as r) = function
    | L_Base b ->
      ovar_of_flat_term_base r b
    | L_Sum (l, o) ->
      let l, o = iexpr_of_sum r l o
      and v = S.new_var r_ctx mip_type_int in
      S.add_eq r_ctx ((Int63.minus_one, v) :: l, o);
      Some v, Int63.zero
    | L_Bool g ->
      (match xvar_of_formula r g with
      | S_Pos (Some v) ->
        Some v, Int63.zero
      | S_Neg (Some v) ->
        Some (S.negate_var r_ctx v), Int63.zero
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
      Some (acc: S.var signed list)

  and blast_conjunction_reduce {r_ctx} l =
    match l with
    | [] ->
      xtrue
    | [S_Pos x] ->
      S_Pos (Some x)
    | [S_Neg x] ->
      S_Neg (Some x)
    | _ ->
      let rval = S.new_var r_ctx mip_type_bool in
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
      S_Pos (Some (var_of_app r f_id l mip_type_bool))
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

  let finally_assert_formula ({r_ctx} as r) = function
    | S_Pos (Some v) ->
      S.add_eq r_ctx ([Int63.one, v], Int63.minus_one)
    | S_Neg (Some v) ->
      S.add_eq r_ctx ([Int63.one, v], Int63.zero)
    | S_Pos None ->
      ()
    | S_Neg None ->
      r.r_unsat <- true

  let new_ivar {r_ctx} =
    S.new_var r_ctx mip_type_int

  let new_bvar {r_ctx} =
    S.new_var r_ctx mip_type_bool

  let assert_formula ({r_q} as r) g =
    Dequeue.push_back r_q (flatten_formula r g)

  let solve ({r_q; r_ctx} as r) =
    Dequeue.iter r_q
      ~f:(Fn.compose
            (finally_assert_formula r)
            (blast_formula r));
    Dequeue.clear r_q;
    if r.r_unsat then
      R_Unsat
    else
      S.solve r_ctx

  let write_bg_ctx {r_ctx} =
    S.write_ctx r_ctx

  let deref_int {r_ctx; r_ivar_m} id =
    match Hashtbl.find r_ivar_m id with
    | Some v ->
      S.deref r_ctx v
    | None ->
      None

  let deref_bool {r_ctx; r_bvar_m} id =
    match Hashtbl.find r_bvar_m id with
    | Some v ->
      Option.map ~f:Int63.((>) one) (S.deref r_ctx v)
    | None ->
      None

end
