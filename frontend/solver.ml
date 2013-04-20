open Core.Std
open Terminology

module Make (S: Imt_intf.S) = struct

  module LA = Lang_abstract

  (* TODO: use herelib for inserting locations *)
  exception Exn_unreachable of string

  type ivar = S.var
  type bvar = S.var
  type var = S.var

  type f = S.f

  type 't term = (bvar, ivar, 't) LA.term

  type ibterm = C_Bool of bool term | C_Int of int term

  type formula = (bvar, ivar) LA.atom Formula.formula

  (* flat internal representation of terms and formulas *)

  type flat_term_sum = (Int63.t * flat_term_base) list

  and flat_term =
    L_Base  of  flat_term_base
  | L_Sum   of  flat_term_sum offset

  and flat_term_base =
    B_Var   of  var
  | B_Bool  of  flat_formula
  | B_App   of  flat_term list
  | B_Ite   of  flat_formula * flat_term * flat_term

  and flat_formula =
    U_Var   of  var
  | U_App   of  flat_term list
  | U_Atom  of  flat_term * op'
  | U_Not   of  flat_formula
  | U_And   of  flat_formula list
  | U_Ite   of  flat_formula * flat_formula * flat_formula

  (* we will expand-out ITE right before blasting *)

  let ff_ite q g h =
    let ff_not = function U_Not g -> g | g -> U_Not g in
    let ff_or a b = U_Not (U_And [ff_not a; ff_not b]) in
    U_And [ff_or (ff_not q) g; ff_or q h]

  (* optional var, possibly negated *)

  type xvar = var option signed

  let xtrue = S_Pos None

  let xfalse = S_Neg None

  (* flatten terms and formulas; SCC impractical to break *)

  let rec flatten_args :
  type s t .
  flat_term list -> (s -> t) term -> flat_term list =
    fun acc -> function
    | LA.M_App (f, t) ->
      flatten_args (flatten_term t :: acc) f
    | LA.M_Fun (_, _) ->
      List.rev acc
    | _ ->
      raise (Exn_unreachable "GADTs confuse exhaustiveness checker")

  and flatten_term_aux_aux :
  type t.
  flat_term_sum offset -> Int63.t -> t term -> flat_term_sum offset =
    fun (d, r) k -> function
    | LA.M_Ivar v ->
      (k, B_Var v) :: d, r
    | LA.M_Int i ->
      d, Int63.(r + k * i)
    | LA.M_App (f, t) ->
      (k, B_App (flatten_args [flatten_term t] f)) :: d, r
    | LA.M_Sum (s, t) ->
      let d, r = flatten_term_aux_aux (d, r) k s in
      flatten_term_aux_aux (d, r) k t
    | LA.M_Prod (k2, t) ->
      flatten_term_aux_aux (d, r) Int63.(k * k2) t
    | LA.M_Ite (c, s, t) ->
      (k, B_Ite (flatten_formula c,
                 flatten_term s,
                 flatten_term t)) :: d, r
    | LA.M_Bool g ->
      (k, B_Bool (flatten_formula g)) :: d, r
    | LA.M_Fun (_, _) ->
      raise (Exn_unreachable "GADTs confuse exhaustiveness checker")

  and flatten_term_aux :
  type t . t term -> flat_term =
    fun t ->
      let d, r = [], Int63.zero in
      let d, r = flatten_term_aux_aux (d, r) Int63.one t in
      (* dedup / sort / hash d here *)
      L_Sum (d, r)

  and flatten_term :
  type t . t term -> flat_term =
    function
    | LA.M_Ivar v ->
      L_Base (B_Var v)
    | LA.M_App (f, t) ->
      L_Base (B_App (flatten_args [flatten_term t] f))
    | LA.M_Ite (c, s, t) ->
      L_Base
        (B_Ite (flatten_formula c, 
                flatten_term s,
                flatten_term t))
    | t ->
      flatten_term_aux t

  and flatten_formula_aux d = function
    | Formula.F_True ->
      d
    | Formula.F_And (g, h) ->
      let d = flatten_formula_aux d g in
      flatten_formula_aux d h
    | g ->
      flatten_formula g :: d

  and flatten_formula = function
    | Formula.F_True ->
      U_And []
    | Formula.F_Atom (LA.A_Le t) ->
      U_Atom (flatten_term t, O'_Le)
    | Formula.F_Atom (LA.A_Eq t) ->
      U_Atom (flatten_term t, O'_Eq)
    | Formula.F_Atom (LA.A_Bool t) ->
      (* FIXME *)
      U_And []
    | Formula.F_Atom (LA.A_Bvar v) ->
      U_Var v
    | Formula.F_Not g ->
      U_Not (flatten_formula g)
    | Formula.F_Ite (q, g, h) ->
      U_Ite (flatten_formula q,
             flatten_formula g,
             flatten_formula h)
    | Formula.F_And (_, _) as g ->
      U_And (flatten_formula_aux [] g)

  type ctx = {
    r_ctx           : S.ctx;
    r_xvar_m        : (flat_formula, xvar) Hashtbl.Poly.t;
    r_q             : flat_formula Dequeue.t;
    mutable r_unsat : bool
  }

  let make_ctx () = {
    r_ctx    = S.new_ctx ();
    r_xvar_m = Hashtbl.Poly.create ~size:10240 ();
    r_q      = Dequeue.create () ~dummy:(U_And []);
    r_unsat  = false
  }

  let mip_type_bool =
    T_Int (Some Int63.zero, Some Int63.one)

  let mip_type_int =
    T_Int (None, None)

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
    S.add_indicator r_ctx vp_gt (s, Int63.(one - o));
    S.add_clause r_ctx [vp; vp_lt; vp_gt];
    S_Pos (Some v)

  and ovar_of_flat_term_base ({r_ctx} as r) = function
    | B_Var v ->
      Some v, Int63.zero
    | B_Bool g ->
      (match xvar_of_formula r g with
      | S_Pos (Some v) ->
        Some v, Int63.zero
      | S_Neg (Some v) ->
        Some (S.get_negated_var r_ctx v), Int63.zero
      | S_Pos None ->
        None, Int63.one
      | S_Neg None ->
        None, Int63.zero)
    | B_App l ->
      (* FIXME f call *)
      let v = S.new_var r_ctx mip_type_int in
      S.add_call  r_ctx (Some v, Int63.zero)
        (S.new_f r_ctx "" 0)
        (List.map l ~f:(ovar_of_flat_term r));
      Some v, Int63.zero
    | B_Ite (g, s, t) ->
      (* FIXME *)
      None, Int63.zero

  and ovar_of_flat_term ({r_ctx} as r) = function
    | L_Base b ->
      ovar_of_flat_term_base r b
    | L_Sum (l, o) ->
      let l, o = iexpr_of_sum r l o
      and v = S.new_var r_ctx mip_type_int in
      S.add_eq r_ctx ((Int63.minus_one, v) :: l, o);
      Some v, Int63.zero

  and blast_atom ({r_ctx} as r) = function
    | L_Base t, O'_Le ->
      blast_le r [Int63.one, t] Int63.zero
    | L_Sum (s, o), O'_Le ->
      blast_le r s o
    | L_Base t, O'_Eq ->
      blast_eq r [Int63.one, t] Int63.zero
    | L_Sum (s, o), O'_Eq ->
      blast_eq r s o

  and blast_conjunction_map r acc = function
    | g :: tail ->
      (match blast_formula r g with
      | S_Pos (Some x) ->
        blast_conjunction_map r ((S_Pos x) :: acc) tail
      | S_Pos None ->
        blast_conjunction_map r acc tail
      | S_Neg (Some x) ->
        blast_conjunction_map r ((S_Neg x) :: acc) tail
      | S_Neg None ->
        None)
    | [] ->
      Some (acc: var signed list)

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
      let f v = S.add_clause r_ctx [S_Neg rval; v] in
      List.iter l ~f;
      S.add_clause r_ctx (S_Pos rval :: List.map l ~f:snot);
      S_Pos (Some rval)

  and blast_conjunction r l =
    Option.value_map (blast_conjunction_map r [] l)
      ~f:(blast_conjunction_reduce r)
      ~default:xfalse

  and blast_formula ({r_ctx} as r) = function
    | U_Var v ->
      S_Pos (Some v)
    | U_App l ->
      (* FIXME; fix int counterpart first and adapt *)
      S_Pos None
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

  let get_ivar {r_ctx} =
    S.new_var r_ctx mip_type_int

  let get_bvar {r_ctx} =
    S.new_var r_ctx mip_type_bool

  let assert_formula {r_q} g =
    Dequeue.push_back r_q (flatten_formula g)

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

  let deref_int {r_ctx} =
    S.deref r_ctx

  let deref_bool r v =
    Option.map ~f:Int63.((>) one) (deref_int r v)

end
