open Core.Std
open Terminology
(* open Core.Int_replace_polymorphic_compare *)

let dbg = false

module Make

  (S : Imt_intf.S_access)
  (I : Id.S) =

struct

  open Logic

  module Matching = Flat.Matching(M)

  module Conv = Flat.Conv(I)(M)

  module Linear = Flat.Linear(I)

  module P = Pre.Make(I)

  type c = I.c

  type 't term = (I.c, 't) M.t

  type formula = I.c A.t Formula.t

  (*

    Types come with boilerplate for comparison and sexp conversion.

    Type_conv can generate these automatically, but it breaks module
    definitions and recursive modules.

  *)

  let hashable_ivar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = S.compare_ivar;
    sexp_of_t = S.sexp_of_ivar
  }

  let hashable_bvar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = S.compare_bvar;
    sexp_of_t = S.sexp_of_bvar
  }

  type fid = I.c Id.Box_arrow.t
  with compare, sexp_of

  let hashable_fid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_fid;
    sexp_of_t = sexp_of_fid
  }

  type iid  = (I.c, int) Id.t
  with compare, sexp_of

  let hashable_iid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_iid;
    sexp_of_t = sexp_of_iid
  }

  type bid = (I.c, bool) Id.t
  with compare, sexp_of

  let hashable_bid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bid;
    sexp_of_t = sexp_of_bid
  }

  type ovar = S.ivar option offset
  with compare, sexp_of

  type bg_call = S.f * ovar list
  with compare, sexp_of

  let compare_bg_call =
    Tuple2.compare
      ~cmp1:S.compare_f
      ~cmp2:(List.compare ~cmp:compare_ovar)

  let sexp_of_bg_call =
    Tuple2.sexp_of_t S.sexp_of_f (List.sexp_of_t sexp_of_ovar)

  let hashable_bg_call = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bg_call;
    sexp_of_t = sexp_of_bg_call;
  }

  type bg_isum = S.ivar isum
  with compare, sexp_of

  let hashable_bg_isum = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash; 
    compare = compare_bg_isum;
    sexp_of_t = sexp_of_bg_isum;
  }

  let flat_sum_negate (l, x) =
    List.map l ~f:(Tuple2.map1 ~f:Int63.neg), Int63.neg x

  (* optional var, possibly negated (S_Pos None means true) *)

  type xvar = S.bvar option signed
  with compare, sexp_of

  let xtrue = S_Pos None

  let xfalse = S_Neg None

  (* axiom-related datatypes *)

  type int_id = (I.c, int) Id.t
  with compare, sexp_of

  type axiom_id = int

  type bind_key = int_id list
  with compare, sexp_of

  type bind_data = (I.c, int) M.t list list

  (* context *)

  type ctx = {
    r_ctx                :  S.ctx;
    r_pre_ctx            :  P.ctx;
    r_ivar_m             :  (iid, S.ivar) Hashtbl.t;
    r_bvar_m             :  (bid, S.bvar) Hashtbl.t;
    r_iid_m              :  (S.ivar, iid) Hashtbl.t;
    r_bid_m              :  (S.bvar, bid) Hashtbl.t;
    r_xvar_m             :  (P.formula, xvar) Hashtbl.t;
    r_fun_m              :  (fid, S.f) Hashtbl.t;
    r_call_m             :  (bg_call, S.ivar) Hashtbl.t;
    r_sum_m              :  (P.sum, S.ivar iexpr) Hashtbl.t;
    r_var_of_sum_m       :  (bg_isum, S.ivar) Hashtbl.t;
    r_ovar_of_iite_m     :  (P.iite, ovar) Hashtbl.t;
    r_patt_m             :
      (c Id.Box_arrow.t, (axiom_id * c Flat.Box.t) list) Hashtbl.t;
    r_bind_m             :
      (axiom_id, (bind_key, bind_data) Hashtbl.t) Hashtbl.t;
    r_axiom_m            :  (axiom_id, c Axiom.Flat.t) Hashtbl.t;
    r_q                  :  P.formula Dequeue.t;
    mutable r_ground_l   :  (I.c, int) M.t list;
    mutable r_obj        :  P.term option;
    mutable r_fun_cnt    :  int;
    mutable r_axiom_cnt  :  int;
    mutable r_unsat      :  bool
  }

  let make_ctx s = {
    r_ctx = s;
    r_pre_ctx = P.make_ctx ();
    r_ivar_m =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_iid;
    r_bvar_m = 
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_bid;
    r_iid_m =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_ivar;
    r_bid_m =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_bvar;
    r_xvar_m =
      Hashtbl.create ()  ~size:10240  ~hashable:P.hashable_formula;
    r_fun_m =
      Hashtbl.create ()  ~size:512    ~hashable:hashable_fid;
    r_call_m =
      Hashtbl.create ()  ~size:2048   ~hashable:hashable_bg_call;
    r_sum_m =
      Hashtbl.create ()  ~size:2048   ~hashable:P.hashable_sum;
    r_var_of_sum_m =
      Hashtbl.create ()  ~size:2048   ~hashable:hashable_bg_isum;
    r_ovar_of_iite_m =
      Hashtbl.create ()  ~size:2048   ~hashable:P.hashable_iite;
    r_axiom_m = Hashtbl.Poly.create () ~size:512;
    r_patt_m = Hashtbl.Poly.create () ~size:1024;
    r_bind_m = Hashtbl.Poly.create () ~size:4096;
    r_q = Dequeue.create () ~initial_length:63;
    r_ground_l = [];
    r_obj = None;
    r_fun_cnt = 0;
    r_axiom_cnt = 0;
    r_unsat = false;
  }

  let get_f ({r_ctx; r_fun_m; r_fun_cnt} as r)
      (Id.Box_arrow.Box id' as id) =
    let default =
      let t = I.type_of_t id' in
      fun () ->
        let s = Printf.sprintf "f_%d" r_fun_cnt in
        r.r_fun_cnt <- r.r_fun_cnt + 1;
        S.new_f r_ctx s (Type.count_arrows t) in
    Hashtbl.find_or_add r_fun_m id ~default

  let get_axiom_id ({r_axiom_cnt} as r) =
    r.r_axiom_cnt <- r.r_axiom_cnt + 1;
    r_axiom_cnt

  let ivar_of_iid {r_ctx; r_ivar_m; r_iid_m} x =
    let default () = 
      let v = S.new_ivar r_ctx in
      Hashtbl.replace r_iid_m v x; v in
    Hashtbl.find_or_add r_ivar_m x ~default

  let bvar_of_bid {r_ctx; r_bvar_m; r_bid_m} x =
    let default () =
      let v = S.new_bvar r_ctx in
      Hashtbl.replace r_bid_m v x; v in
    Hashtbl.find_or_add r_bvar_m x ~default

  let iid_of_ivar {r_iid_m} = Hashtbl.find r_iid_m

  let bid_of_bvar {r_bid_m} = Hashtbl.find r_bid_m

  (* linearizing terms and formulas: utilities before we get into the
     mutually recursive part *)

  let snot = function
    | S_Pos x -> S_Neg x
    | S_Neg x -> S_Pos x

  let negate_isum =
    List.map ~f:(Tuple2.map1 ~f:Int63.neg)

  (* linearizing terms and formulas: mutual recursion, because terms
     contain formulas and vice versa *)

  let rec iexpr_of_sum ({r_sum_m} as r) (l, o) =
    let l, o' =
      let default () =
        let f (l, o) (c, t) =
          match ovar_of_flat_term_base r t with
          | Some v, x ->
            (c, v) :: l, Int63.(o + c * x)
          | None, x ->
            l, Int63.(o + c * x)
        and init = [], Int63.zero in
        List.fold_left ~init ~f l in
      Hashtbl.find_or_add r_sum_m l ~default in
    l, Int63.(o' + o)

  and iexpr_of_flat_term r = function
    | P.G_Sum s ->
      iexpr_of_sum r s
    | P.G_Base b ->
      match ovar_of_flat_term_base r b with
      | Some v, x ->
        [Int63.one, v], x
      | None, x ->
        [], x

  and blast_le ?v ({r_ctx} as r) s =
    let l, o = iexpr_of_sum r s
    and v = match v with Some v -> v | _ -> S.new_bvar r_ctx in
    S.add_indicator r_ctx (S_Pos v)  l                Int63.(neg o);
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

  and var_of_app ?lb ?ub ({r_ctx; r_call_m} as r) f_id l =
    let f = get_f r f_id
    and l = List.map l ~f:(ovar_of_ibeither r) in
    let default () =
      let v = S.new_ivar r_ctx ?lb ?ub in
      S.add_call r_ctx (Some v, Int63.zero) f l;
      v in
    Hashtbl.find_or_add r_call_m (f, l) ~default

  and var_of_bool_app r f_id l =
    (let lb = Int63.zero and ub = Int63.one in
     var_of_app ~lb ~ub r f_id l) |>
        S.bvar_of_ivar

  and blast_ite_branch ({r_ctx} as r) xv v e =
    let l, o = iexpr_of_flat_term r e in
    let l = (Int63.minus_one, v) :: l in
    S.add_indicator r_ctx xv  l                (Int63.neg o);
    S.add_indicator r_ctx xv  (negate_isum l)  o

  and ovar_of_ite ({r_ctx; r_ovar_of_iite_m} as r) ((g, s, t) as i) =
    let default () =
      match xvar_of_formula_doit r g with
      | S_Pos None ->
        ovar_of_term r s
      | S_Neg None ->
        ovar_of_term r t
      | S_Pos (Some bv) ->
        let v = S.new_ivar ~implied_int:true r_ctx in
        blast_ite_branch r (S_Pos bv) v s;
        blast_ite_branch r (S_Neg bv) v t;
        Some v, Int63.zero
      | S_Neg (Some bv) ->
        let v = S.new_ivar ~implied_int:true r_ctx in
        blast_ite_branch r (S_Neg bv) v s;
        blast_ite_branch r (S_Pos bv) v t;
        Some v, Int63.zero in
    Hashtbl.find_or_add r_ovar_of_iite_m i ~default

  and ovar_of_flat_term_base r = function
    | P.B_Var v ->
      Some (ivar_of_iid r v), Int63.zero
    | P.B_Formula g ->
      ovar_of_formula r g
    | P.B_App (f_id, l) ->
      Some (var_of_app r f_id l), Int63.zero
    | P.B_Ite i ->
      ovar_of_ite r i

  and ovar_of_sum {r_ctx; r_var_of_sum_m} = function
    | [], o ->
      None, o
    | [c, x], o when Int63.(c = one) ->
      Some x, o
    | l, o ->
      let v =
        let default () =
          let v = S.new_ivar ~implied_int:true r_ctx in
          S.add_eq r_ctx ((Int63.minus_one, v) :: l) Int63.zero;
          v in
        Hashtbl.find_or_add r_var_of_sum_m l ~default in
      Some v, o
        
  and ovar_of_term r = function
    | P.G_Base b ->
      ovar_of_flat_term_base r b
    | P.G_Sum s ->
      iexpr_of_sum r s |> ovar_of_sum r

  and ovar_of_formula ({r_ctx} as r) g =
    match xvar_of_formula_doit r g with
    | S_Pos (Some v) ->
      Some (S.ivar_of_bvar v), Int63.zero
    | S_Pos None ->
      None, Int63.one
    | S_Neg v ->
      (let f v = S.ivar_of_bvar (S.negate_bvar r_ctx v) in
       Option.map v ~f), Int63.zero

  and ovar_of_ibeither ({r_ctx} as r) = function
    | H_Int (P.G_Base b) ->
      ovar_of_flat_term_base r b
    | H_Int (P.G_Sum s) ->
      (match iexpr_of_sum r s with
      | [], o ->
        None, o
      | [c, x], o when Int63.(c = one) ->
        Some x, o
      | l, o ->
        let v = S.new_ivar ~implied_int:true r_ctx in
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
      (match xvar_of_formula_doit r g with
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

  and blast_conjunction_reduce {r_ctx} = function
    | [] ->
      xtrue
    | [S_Pos x] ->
      S_Pos (Some x)
    | [S_Neg x] ->
      S_Neg (Some x)
    | l ->
      let rval = S.new_bvar r_ctx in
      (let f v = S.add_clause r_ctx [S_Neg rval; v] in
       List.iter l ~f);
      S.add_clause r_ctx (S_Pos rval :: List.map l ~f:snot);
      S_Pos (Some rval)

  and blast_conjunction r l =
    blast_conjunction_map r [] l |>
        (let f = blast_conjunction_reduce r and default = xfalse in
         Option.value_map ~f ~default)

  and blast_formula r = function
    | P.U_Not _
    | P.U_Ite (_, _, _) ->
      raise (Unreachable.Exn _here_)
    | P.U_Var v ->
      S_Pos (Some (bvar_of_bid r v))
    | P.U_App (f_id, l) ->
      S_Pos (Some (var_of_bool_app r f_id l))
    | P.U_Atom (t, o) ->
      blast_atom r (t, o)
    | P.U_And l ->
      blast_conjunction r l

  and xvar_of_formula_doit ({r_ctx; r_xvar_m} as r) = function
    | P.U_Not g ->
      snot (xvar_of_formula_doit r g)
    | P.U_Ite (q, g, h) ->
      let v = P.ff_ite q g h |> xvar_of_formula_doit r in
      (match v with
      | S_Pos (Some v) | S_Neg (Some v) ->
        S.set_bvar_priority r_ctx v 20;
      | _ ->
        ());
      v
    | g ->
      let default () = blast_formula r g in
      Hashtbl.find_or_add r_xvar_m g ~default

  let assert_ivar_equal_constant {r_ctx} v c =
    S.add_eq r_ctx [Int63.one, v] c

  let assert_ivar_le_constant {r_ctx} v c =
    S.add_le r_ctx [Int63.one, v] c

  let assert_bvar_equal_constant {r_ctx} v c =
    let v = S.ivar_of_bvar v
    and c = Int63.(if c then one else zero) in
    S.add_eq r_ctx [Int63.one, v] c

  let finally_assert_unit ({r_ctx} as r) = function
    | S_Pos (Some v) ->
      assert_bvar_equal_constant r v true
    | S_Neg (Some v) ->
      assert_bvar_equal_constant r v false
    | S_Pos None ->
      ()
    | S_Neg None ->
      r.r_unsat <- true

  let rec finally_assert_formula ({r_ctx} as r) = function
    | P.U_And l ->
      List.iter l ~f:(finally_assert_formula r)
    | P.U_Not (P.U_And l) ->
      let f = function
        | [] ->
          r.r_unsat <- true
        | [S_Pos v] ->
          assert_bvar_equal_constant r v false
        | [S_Neg v] ->
          assert_bvar_equal_constant r v true
        | l ->
          (let f = snot in List.map l ~f) |> S.add_clause r_ctx in
      Option.iter (blast_conjunction_map r [] l) ~f
    | P.U_Var v ->
      assert_bvar_equal_constant r (bvar_of_bid r v) true
    | P.U_App (f_id, l) ->
      let v = var_of_bool_app r f_id l in
      assert_bvar_equal_constant r v true
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
      xvar_of_formula_doit r g |> finally_assert_unit r

  let negate_bvar {r_ctx} =
    S.negate_bvar r_ctx

  let xvar_of_formula ({r_pre_ctx} as r) g =
    let g = P.flatten_formula r_pre_ctx g in
    lazy (xvar_of_formula_doit r g)

  let xvar_of_term ({r_pre_ctx} as r) m =
    let m = P.flatten_bool_term r_pre_ctx m in
    lazy (xvar_of_formula_doit r m)

  let ovar_of_term ({r_pre_ctx} as r) m =
    let m = P.flatten_int_term r_pre_ctx m in
    lazy (ovar_of_term r m)

  let bvar_of_id = bvar_of_bid

  let write_bg_ctx {r_ctx} =
    S.write_ctx r_ctx

  let bg_assert_all_cached ({r_q} as r) =
    Dequeue.iter r_q ~f:(finally_assert_formula r);
    Dequeue.clear r_q

  let add_objective ({r_obj; r_pre_ctx} as r) o =
    match r_obj with
    | None ->
      let m = P.flatten_int_term r_pre_ctx o in
      r.r_obj <- Some m; `Ok
    | Some _ ->
      `Duplicate

  let deref_int {r_ctx; r_ivar_m} id =
    Option.(Hashtbl.find r_ivar_m id >>= S.ideref r_ctx)

  let deref_bool {r_ctx; r_bvar_m} id =
    Option.(Hashtbl.find r_bvar_m id >>= S.bderef r_ctx)

  (* local axioms implementation *)

  let bind_for_axiom {r_axiom_m; r_bind_m} axiom_id bindings =
    let key, data = List.unzip bindings
    and axiom = Hashtbl.find r_axiom_m axiom_id in
    let q, _, _ = Option.value_exn axiom ~here:_here_ in
    if
      let f id =
        let f id' = compare_int_id id id' = 0 in
        List.exists q ~f in
      List.for_all key ~f
    then
      let h =
        let default () = Hashtbl.Poly.create () ~size:128 in
        Hashtbl.find_or_add r_bind_m axiom_id ~default
      and f = function
        | Some l ->
          Some
            (if let f = (=) data in List.exists l ~f then
                l
             else
                data :: l)
        | None ->
          Some [data] in
      Hashtbl.change h key f
    else
      ()

  let register_app_for_axioms ({r_patt_m} as r) (m : (c, int) M.t) =
    match m with
    | M.M_App (a, b) ->
      Option.value_exn ~here:_here_ (M.fun_id_of_app m) |>
          Hashtbl.find r_patt_m |>
              let f (axiom_id, Flat.Box.Box pattern) =
                let f l =
                  let f = function
                    | `Bool (_, _) ->
                (* FIXME: let's deal with integers first *)
                      raise (Unreachable.Exn _here_)
                    | `Int (id, m) ->
                      id, m
                  and f' =
                    let cmp (id1, _) (id2, _) =
                      compare_int_id id1 id2 in
                    List.sort ~cmp in
                  List.map l ~f |> f' |> bind_for_axiom r axiom_id in 
                Matching.do_for_match m ~pattern ~f in
              let f = List.iter ~f in
              Option.iter ~f
    | _ ->
      raise (Unreachable.Exn _here_)

  let rec register_apps_term :
  type s. ctx -> (I.c, s) M.t -> unit =
    fun r -> function
    | M.M_Int _ ->
      ()
    | M.M_Var _ ->
      ()
    | M.M_Bool g ->
      register_apps_formula r g
    | M.M_Sum (a, b) ->
      register_apps_term r a; register_apps_term r b
    | M.M_Prod (_, a) ->
      register_apps_term r a
    | M.M_Ite (g, a, b) ->
      register_apps_formula r g;
      register_apps_term r a;
      register_apps_term r b
    | M.M_App (a, b) as m ->
      (match M.type_of_t m with
      | Type.Y_Int ->
        register_app_for_axioms r m
      | _ ->
        ());
      register_apps_term r a;
      register_apps_term r b

  and register_apps_formula r =
    let f a ~polarity =
      match a with
      | A.A_Bool m ->
        register_apps_term r m
      | A.A_Le m | A.A_Eq m ->
        register_apps_term r m
    and polarity = `Both in
    Formula.iter_atoms ~f ~polarity

  let register_axiom_terms {r_patt_m} id axiom =
    let open Flat in
    let f = function
      | M_Var _ ->
        ()
      | M_App (_, _) as m ->
        let key = Option.value_exn (fun_id_of_app m) ~here:_here_
        and data = id, Flat.Box.Box m in
        Hashtbl.add_multi r_patt_m ~key ~data in
    Axiom.Flat.iter_subterms axiom ~f

  let instantiate r (l, o) ~bindings =
    let f (l, s) (c, m) =
      Conv.term_of_t m ~bindings |>
          ovar_of_term r |>
              Lazy.force |>
                  function
                  | Some v, o ->
                    (c, v) :: l, Int63.(s + c * o)
                  | None, o ->
                    l,  Int63.(s + c * o)
    and init = [], o in
    List.fold_left l ~f ~init

  let bindings_of_substitution =
    let f x = `Int x in
    List.map ~f

  let rec iter_substitutions r axiom_id h keys ~f ~bound =
    match keys with
    | a :: d ->
      let l = Option.value_exn (Hashtbl.find h a) ~here:_here_
      and f a' =
        let bound =
          Option.value_exn (List.zip a a') ~here:_here_ |>
              List.append bound in
        iter_substitutions r axiom_id h d ~f ~bound in
      List.iter l ~f
    | [] ->
      f (List.rev bound)

  let iter_substitutions ({r_axiom_m; r_bind_m} as r) axiom_id ~f =
    let f h =
      let bound = [] in
      iter_substitutions r axiom_id h (Hashtbl.keys h) ~f ~bound in
    Option.iter (Hashtbl.find r_bind_m axiom_id) ~f

  let encode_all_axiom_instances ({r_ctx; r_axiom_m} as r) =
    let cnt = ref 0 in
    let f ~key ~data:(q, l, c) =
      let f s =
        let bindings = bindings_of_substitution s in
        let f (a, b) =
          let f x =
            instantiate r ~bindings x |> ovar_of_sum r in
          let v_a, o_a = f a in
          f b, (v_a, Int63.(o_a - one)) in
        let l = List.map l ~f
        and c =
          instantiate r ~bindings c |> ovar_of_sum r in
        let l = (c, (None, Int63.zero)) :: l in
        S.add_diffs_disjunction r_ctx l;
        incr cnt in
      iter_substitutions r key ~f in
    Hashtbl.iter r_axiom_m ~f;
    if dbg then Printf.printf "[INFO] %d axiom instances\n%!" !cnt

  let cut_of_term m ~bindings =
    let open Option in
    let f acc c m =
      acc >>= (fun (l, bindings) ->
        Conv.t_of_term m ~bindings >>| (fun (m, bindings) ->
          (c, m) :: l, bindings))
    and f_offset acc o =
      acc >>| (fun (l, bindings) -> (l, o), bindings)
    and init = Some ([], bindings)
    and factor = Int63.one in
    M.fold_sum_terms m ~f ~f_offset ~init ~factor

  let negate_cut (l, o) =
    let f (c, x) = Int63.(~-) c, x
    and o = Int63.(~-) o in
    List.map l ~f, o

  let linearize_iexpr (l, o) ~quantified ~map ~copies =
    let l, map, copies =
      let f (l, map, copies) (c, under) =
        let under, map, copies =
          Linear.linearize under ~quantified ~under ~map ~copies in
        (c, under) :: l, map, copies
      and init = [], map, copies in
      List.fold_left l ~init ~f in
    let l = List.rev l in
    (l, o), map, copies

  let linearize_axiom (quantified, h, cut) =
    let map = Map.Poly.empty and copies = [] in
    let h, map, copies =
      let f (l, map, copies) (a, b) =
        let a, map, copies =
          linearize_iexpr a ~quantified ~map ~copies in
        let b, map, copies =
          linearize_iexpr b ~quantified ~map ~copies in
        (a, b) :: l, map, copies
      and init = [], map, copies in
      List.fold_left h ~f ~init in
    let cut, map, copies =
      linearize_iexpr cut ~quantified ~map ~copies in
    let h =
      let f (a, b) =
        let open Int63 in
        ([one, Flat.M_Var a], zero),
        ([one, Flat.M_Var b], zero) in
      List.rev_map_append copies (List.rev_map_append copies h ~f)
        ~f:(Fn.compose f Tuple.T2.swap)
    and quantified =
      let f (id, _) = id in
      List.rev_map_append copies quantified ~f in
    quantified, h, cut

  let flatten_axiom (q, (l, (c1, c2, op))) =
    let open Option in (
      let f acc (m1, m2, op) =
        acc >>= (fun (l, bindings) ->
          Conv.sum_of_term m1 ~bindings >>= (fun (s1, bindings) ->
            Conv.sum_of_term m2 ~bindings >>| (fun (s2, bindings) ->
              (match op with
              | Terminology.O'_Le ->
                (s1, s2) :: l
              | Terminology.O'_Eq ->
                (s1, s2) :: (s2, s1) :: l), bindings)))
      and init = Some ([], []) in
      List.fold_left l ~init ~f) >>= (fun (init, bindings) ->
        M.(c1 - c2) |>
            cut_of_term ~bindings >>| (fun (c, bindings) ->
              let q =
                let f = Tuple.T2.get1 in
                List.rev_map_append bindings q ~f
              and h =
                let f acc (id, def) =
                  let e = Int63.([one, Flat.M_Var id], zero) in
                  (e, def) :: (def, e) :: acc in
                List.fold_left bindings ~f ~init in
              (match op with
              | Terminology.O'_Le ->
                [q, h, c]
              | Terminology.O'_Eq ->
                [q, h, c; q, h, negate_cut c])))

  let rec int_args :
  type s t .
  (I.c, s -> t) M.t -> acc:(I.c, int) M.t list ->
    (I.c, int) M.t list =
    fun m ~acc ->
      match m with
      | M.M_App (f, x) ->
        (match M.type_of_t x with
        | Type.Y_Int ->
          let acc = x :: acc in
          int_args f ~acc
        | _ ->
          int_args f ~acc)
      | M.M_Var _ ->
        acc

  let rec maximal_ground_subterms :
  type s . ctx -> I.c Axiom.quantified list ->
    (I.c, s) M.t -> acc:(I.c, int) M.t list ->
    bool * (I.c, int) M.t list =
    fun r q m ~acc ->
      match m with
      | M.M_Bool _ ->
        false, acc
      | M.M_Ite _ ->
        false, acc
      | M.M_Int _ ->
        true, acc
      | M.M_Sum (a, b) ->
        let a_b, acc = maximal_ground_subterms r q a ~acc in
        let b_b, acc = maximal_ground_subterms r q b ~acc in
        (match a_b, b_b with
        | true, true ->
          true, acc
        | true, false ->
          false, a :: acc
        | false, true ->
          false, b :: acc
        | _, _ ->
          false, acc)
      | M.M_App (a, b) ->
        let a_b, acc = maximal_ground_subterms r q a ~acc in
        let b_b, acc = maximal_ground_subterms r q b ~acc in
        (match a_b, b_b with
        | true, true ->
          true, acc
        | false, true ->
          false,
          (match M.type_of_t b with
          | Type.Y_Int ->
            b :: acc
          | _ ->
            acc)
        | true, false ->
          false, int_args a ~acc
        | _, _ ->
          false, acc)
      | M.M_Prod (_, a) ->
        maximal_ground_subterms r q a ~acc
      | M.M_Var v ->
        (match Id.type_of_t v with
        | Type.Y_Int ->
          let f = (=) v in
          not (List.exists q ~f), acc
        | Type.Y_Int_Arrow _ ->
          true, acc
        | Type.Y_Bool_Arrow _ ->
          true, acc
        | _ ->
          false, acc)

  let record_axiom_ground_terms r ((q, _) as axiom) =
    let l =
      let f acc m =
        let b, acc = maximal_ground_subterms r q m ~acc in
        if b then m :: acc else acc
      and init = [] in
      Axiom.X.fold_terms axiom ~f ~init in
    let l =
      let f = function
        | M.M_App (_, _) ->
          true
        | _ ->
          false in
      List.filter l ~f in
    r.r_ground_l <- List.append l r.r_ground_l
      
  let assert_axiom ({r_axiom_m} as r) axiom =
    record_axiom_ground_terms r axiom;
    match flatten_axiom axiom with
    | Some axioms ->
      let f axiom =
        let axiom = linearize_axiom axiom in
        let id = get_axiom_id r in
        Hashtbl.replace r_axiom_m id axiom;
        register_axiom_terms r id axiom in
      List.iter axioms ~f; `Ok
    | None ->
      `Unsupported

  let assert_formula ({r_pre_ctx; r_q} as r) g =
    register_apps_formula r g;
    P.flatten_formula r_pre_ctx g |> Dequeue.enqueue_back r_q

  let solve ({r_ctx; r_obj; r_ground_l} as r) =
    bg_assert_all_cached r;
    (let f = register_apps_term r in
     List.iter r_ground_l ~f);
    encode_all_axiom_instances r;
    match r_obj, r.r_unsat with
    | _, true ->
      R_Unsat
    | Some o, false ->
      let l, _ = iexpr_of_flat_term r o in
      (match S.add_objective r_ctx l with
      | `Duplicate ->
        raise (Unreachable.Exn _here_)
      | `Ok ->
        S.solve r_ctx)
    | None, false ->
      S.solve r_ctx

end
