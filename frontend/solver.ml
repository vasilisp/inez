open Core.Std
open Terminology

module Make (S: Imt_intf.S) = struct

  module IL = Inez_logic

  type var = S.var

  type f = S.f

  type term = (f, var) IL.term

  type formula = (f, var) IL.atom Formula.formula

  (* Flat internal representation of terms and formulas. *)

  type flat_term =
    L_Base  of  flat_term_base
  | L_Sum   of  (Int63.t * flat_term_base) list * Int63.t

  and flat_term_base =
    B_Var  of  var
  | B_App  of  f * flat_term list
  | B_Ite  of  flat_formula * flat_term * flat_term

  and flat_formula =
    U_Atom  of  flat_term * op' option
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

  let rec flatten_term_aux_aux (d, r) k = function
    | IL.M_Var v ->
      (k, B_Var v) :: d, r
    | IL.M_Int i ->
      d, Int63.(r + k * i)
    | IL.M_App (ff, l) ->
      let l = List.map l ~f:flatten_term in
      (k, B_App (ff, l)) :: d, r
    | IL.M_Sum (s, t) ->
      let d, r = flatten_term_aux_aux (d, r) k s in
      flatten_term_aux_aux (d, r) k t
    | IL.M_Prod (k2, t) ->
      flatten_term_aux_aux (d, r) Int63.(k * k2) t
    | IL.M_Ite (c, s, t) ->
      (k, B_Ite (flatten_formula c,
                 flatten_term s,
                 flatten_term t)) :: d, r

  and flatten_term_aux term =
    let d, r = [], Int63.zero in
    let d, r = flatten_term_aux_aux (d, r) Int63.one term in
    (* dedup / sort / hash d here *)
    L_Sum (d, r)

  and flatten_term = function
    | IL.M_Var v ->
      L_Base (B_Var v)
    | IL.M_App (f, l) ->
      L_Base (B_App (f, List.map l ~f:(flatten_term)))
    | IL.M_Ite (c, s, t) ->
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
    | Formula.F_Atom (a, op) ->
      U_Atom (flatten_term a, op)
    | Formula.F_Not g ->
      U_Not (flatten_formula g)
    | Formula.F_Ite (q, g, h) ->
      U_Ite (flatten_formula q,
             flatten_formula g,
             flatten_formula h)
    | Formula.F_And (_, _) as g ->
      U_And (flatten_formula_aux [] g)

  type ctx = {
    r_ctx    : S.ctx;
    r_xvar_m : (flat_formula, xvar) Hashtbl.Poly.t;
    r_q      : flat_formula Dequeue.t
  }

  let make_ctx () = {
    r_ctx    = S.new_ctx ();
    r_xvar_m = Hashtbl.Poly.create ~size:10240 ();
    r_q      = Dequeue.create () ~dummy:(U_And []);
  }

  let mip_type_bool =
    T_Int (Some Int63.zero, Some Int63.one)

  (* flatten terms *)

  (* linearizing terms and formulas: utilities before we get into the
     mutually recursive part *)

  let snot = function
    | S_Pos x -> S_Neg x
    | S_Neg x -> S_Pos x

  (* linearizing terms and formulas: mutual recursion, because terms
     contain formulas and vice versa *)

  let rec ovar_of_flat_term_base ({r_ctx} as r) = function
    | B_Var v ->
      ignore r;
      Some v, Int63.zero
    | B_App _ ->
      (* FIXME *)
      None, Int63.zero
    | B_Ite (g, s, t) ->
      (* FIXME *)
      None, Int63.zero

  and ovar_of_flat_term ({r_ctx} as r) = function
    | L_Base b ->
      ignore r;
      ovar_of_flat_term_base r b
    | L_Sum (l, o) ->
      (* FIXME *)
      None, Int63.zero

  and blast_atom ({r_ctx} as r) t o =
    (* FIXME *)
    ignore r;
    S_Pos None

  and blast_and_map r acc = function
    | g :: tail ->
      (match blast_formula r g with
      | S_Pos (Some x) ->
        blast_and_map r ((S_Pos x) :: acc) tail
      | S_Pos None ->
        blast_and_map r acc tail
      | S_Neg (Some x) ->
        blast_and_map r ((S_Neg x) :: acc) tail
      | S_Neg None ->
        None)
    | [] ->
      Some (acc: var signed list)

  and blast_and_reduce {r_ctx} l =
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

  and blast_and r l =
    Option.value_map (blast_and_map r [] l)
      ~f:(blast_and_reduce r)
      ~default:xfalse

  and blast_formula ({r_ctx} as r) = function
    | U_Atom (t, o) ->
      blast_atom r t o
    | U_Not g ->
      snot (blast_formula r g)
    | U_And l ->
      blast_and r l
    | U_Ite (q, g, h) ->
      blast_formula r (ff_ite q g h)

  and xvar_of_formula ({r_xvar_m} as r) g =
    let default () = blast_formula r g in
    Hashtbl.find_or_add r_xvar_m g ~default

  let assert_formula {r_q} g =
    Dequeue.push_back r_q (flatten_formula g)

  let solve ({r_q} as r) =
    Dequeue.iter r_q ~f:(Fn.compose ignore (blast_formula r));
    Dequeue.clear r_q;
    R_Sat

end
