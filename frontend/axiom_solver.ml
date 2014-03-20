open Core.Std
open Logic

module Matching = Flat.Matching(M)

module Conv = Flat.Conv(M)

module Make (Imt : Imt_intf.S_with_cut_gen) (I : Id.S) = struct

  module Lt = Lt.Make(Imt)

  module Imt' = Imt.F(Lt)

  module S = Solver.Make(Imt')(I)
  
  type c = I.c

  type mono_id = (I.c, int -> int) Id.t

  type int_term = (I.c, int) M.t

  type formula = I.c A.t Formula.t

  type app = int_term * int_term

  type ovar = Imt.ivar option Terminology.offset
  with compare, sexp_of

  type ovov = ovar * ovar    
  with compare, sexp_of

  type aocc = Lt.axiom_id * Imt.Dvars.t list
  with compare, sexp_of

  let hashable_ovov = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_ovov;
    sexp_of_t = sexp_of_ovov
  }

  let hashable_aocc = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_aocc;
    sexp_of_t = sexp_of_aocc
  }

  (* FIXME : monomorphic tables / sets *)

  type binding = (c, int) Id.t * (c, int) M.t 

  type ctx = {
    r_ctx       :  S.ctx;
    r_lt_ctx    :  Lt.ctx;
    r_imt_ctx   :  Imt'.ctx;
    r_a_h       :  (Lt.axiom_id, c Axiom.t) Hashtbl.t;
    r_a_patt_h  :
      (c Id.Box_arrow.t, (Lt.axiom_id * c Flat.Box.t) list)
      Hashtbl.t;
    r_a_bind_h  :
      (Lt.axiom_id,
       ((c, int) Id.t, (c, int) M.t list) Hashtbl.t)
      Hashtbl.t;
    r_a_occ_h   :  (aocc, binding list list) Hashtbl.t;
    r_f_h       :  (mono_id, app Hash_set.t) Hashtbl.t;
    r_dvars_h   :  (ovov, Imt.Dvars.t) Hashtbl.t;
    r_occ_h     :  (Imt.Dvars.t, (ovar * ovar) list) Hashtbl.t;
    r_q         :  formula Dequeue.t
  }

  let make_ctx () =
    let r_f_h       =  Hashtbl.Poly.create () ~size:128
    and r_lt_ctx    =  Lt.make_ctx () in
    let r_imt_ctx   =  Imt'.make_ctx r_lt_ctx in
    let r_ctx       =  S.make_ctx r_imt_ctx
    and r_a_h       =  Hashtbl.Poly.create () ~size:32
    and r_a_patt_h  =  Hashtbl.Poly.create () ~size:1024
    and r_a_bind_h  =  Hashtbl.Poly.create () ~size:4096
    and r_a_occ_h   =
      Hashtbl.create () ~size:4096 ~hashable:hashable_aocc;
    and r_dvars_h   =
      Hashtbl.create () ~size:2048 ~hashable:hashable_ovov
    and r_occ_h     =
      Hashtbl.create () ~size:2048 ~hashable:Imt.Dvars.hashable
    and r_q         =  Dequeue.create () in
    {r_ctx; r_lt_ctx; r_imt_ctx;
     r_a_h; r_a_patt_h; r_a_bind_h; r_a_occ_h;
     r_f_h; r_dvars_h; r_occ_h; r_q}

  let mono_increasing {r_f_h} (f : (I.c, int -> int) Id.t) =
    let default () = Hash_set.Poly.create () ~size:128 in
    ignore (Hashtbl.find_or_add r_f_h f ~default)

  let assert_formula {r_ctx; r_q} g =
    Dequeue.enqueue_back r_q g

  let bind_for_axiom {r_a_h; r_a_bind_h} axiom_id key data =
    let axiom = Hashtbl.find r_a_h axiom_id in
    let q, _, _ = Option.value_exn axiom ~here:_here_ in
    if List.exists q ~f:((=) key) then
      let h =
        let default () = Hashtbl.Poly.create () ~size:128 in
        Hashtbl.find_or_add r_a_bind_h axiom_id ~default in
      Hashtbl.add_multi h ~key ~data
    else
      ()

  let register_app_for_axioms ({r_a_patt_h} as r) (m : (c, int) M.t) =
    match m with
    | M.M_App (a, b) ->
      let f axiom_id = function
        | `Bool (_, _) ->
          (* FIXME: let's deal with integers first *)
          raise (Unreachable.Exn _here_)
        | `Int (id, m) ->
          bind_for_axiom r axiom_id id m in
      let f axiom_id =
        List.iter ~f:(f axiom_id) in
      let f (axiom_id, Flat.Box.Box pattern) =
        Matching.do_for_match m ~pattern ~f:(f axiom_id) in
      let f = List.iter ~f
      and o =
        let key = M.fun_id_of_app m in
        let key = Option.value_exn key ~here:_here_ in
        Hashtbl.find r_a_patt_h key in
      Option.iter o ~f
    | _ ->
      raise (Unreachable.Exn _here_)

  let rec iter_substitutions r axiom_id h q ~f ~bound =
    match q with
    | a :: d ->
      let f l =
        let f m =
          let bound = (a, m) :: bound in
          iter_substitutions r axiom_id h d ~f ~bound in
        List.iter l ~f in
      Option.iter (Hashtbl.find h a) ~f
    | [] ->
      f bound

  let iter_substitutions ({r_a_h; r_a_bind_h} as r) axiom_id ~f =
    match
      Hashtbl.find r_a_h axiom_id,
      Hashtbl.find r_a_bind_h axiom_id
    with
    | Some (q, _, _), Some h ->
      iter_substitutions r axiom_id h q ~f ~bound:[]
    | _, _ ->
      ()

  let get_dvar {r_imt_ctx; r_dvars_h} ov1 ov2 =
    let default () = Imt.Dvars.create_dvar r_imt_ctx ov1 ov2 in
    Hashtbl.find_or_add r_dvars_h (ov1, ov2) ~default

  let register_all_axiom_terms
      ({r_ctx; r_lt_ctx; r_a_h; r_a_occ_h} as r) =
    let f ~key ~data:(q, l, c) =
      let f substitution =
        let bindings = List.map substitution ~f:(fun x -> `Int x) in
        let f ((a, b), o) =
          let f a =
            Lazy.force
              (S.ovar_of_term r_ctx (Conv.term_of_t a ~bindings))
          and default = None, Int63.zero in
          let a = f a
          and b = Option.value_map b ~f ~default in
          get_dvar r a b in
        let dvars = List.map l ~f in
        Lt.assert_instance r_lt_ctx key dvars;
        Hashtbl.add_multi r_a_occ_h (key, dvars) substitution in
      iter_substitutions r key ~f in
    Hashtbl.iter r_a_h ~f
  
  let rec register_apps_formula ({r_ctx; r_f_h} as r) g =
    let rec f : type s . (I.c, s) M.t -> unit = function
      | M.M_Int _ ->
        ()
      | M.M_Var _ ->
        ()
      | M.M_Bool g ->
        register_apps_formula r g
      | M.M_Sum (a, b) ->
        f a; f b
      | M.M_Prod (_, a) ->
        f a
      | M.M_Ite (g, a, b) ->
        register_apps_formula r g; f a; f b
      | M.M_App (M.M_Var id, a) as a' ->
        (match I.type_of_t id with
        | Type.Y_Int_Arrow Type.Y_Int ->
          let f = Fn.flip Hash_set.add (a, a') in
          Option.iter (Hashtbl.find r_f_h id) ~f;
          register_app_for_axioms r a'
        | _ ->
          ()); f a
      | M.M_App (a, b) as m ->
        (match M.type_of_t m with
        | Type.Y_Int ->
          register_app_for_axioms r m
        | _ ->
          ());
        f a; f b in
    let f a ~polarity =
      match a with
      | A.A_Bool m ->
        f m
      | A.A_Le m | A.A_Eq m ->
        f m
    and polarity = `Both in
    Formula.iter_atoms g ~f ~polarity

  let assert_instance_lt ({r_lt_ctx; r_imt_ctx; r_occ_h} as r)
      id (ov1, ovr1) (ov2, ovr2) =
    let dv = get_dvar r ov1 ov2 in
    Hashtbl.add_multi r_occ_h dv (ovr1, ovr2);
    Lt.assert_instance r_lt_ctx id [dv]

  let register_diffs ({r_ctx; r_imt_ctx; r_f_h} as r) id =
    let f ~key ~data =
      let f = Fn.compose Lazy.force (S.ovar_of_term r_ctx) in
      let f (v1, v2) = f v1, f v2 in
      (* FIXME : avoid conversion *)
      let data = Hash_set.to_list data in
      let data = List.map data ~f in
      let f pair1 pair2 =
        assert_instance_lt r id pair1 pair2;
        assert_instance_lt r id pair2 pair1 in
      Util.iter_pairs data ~f in
    Hashtbl.iter r_f_h ~f

  let get_cut_base v1 v2 =
    match v1, v2 with
    | Some v1, Some v2 ->
      assert (not (Imt.compare_ivar v1 v2 = 0));
      [Int63.one, v1; Int63.minus_one, v2]
    | Some v1, None ->
      [Int63.one, v1]
    | None, Some v2 ->
      [Int63.minus_one, v2]
    | None, None ->
      []

  let get_cut (v1, o1) (v2, o2) =
    get_cut_base v1 v2, Int63.(o1 - o2)

  let get_cuts r_occ_h _ = function
    | [dv] ->
      (match Hashtbl.find r_occ_h dv with
      | Some l ->
        List.map l ~f:(Tuple.T2.uncurry get_cut)
      | None ->
        [])
    | _ ->
      []

  let register_axiom_terms {r_a_patt_h} id axiom =
    let open Flat in
    let f = function
      | M_Var _ ->
        ()
      | M_App (_, _) as m ->
        let key = fun_id_of_app m in
        let key = Option.value_exn key ~here:_here_
        and data = id, Flat.Box.Box m in
        Hashtbl.add_multi r_a_patt_h ~key ~data in
    Axiom.iter_subterms axiom ~f

  let instantiate {r_ctx; r_a_h; r_a_occ_h} id dvars =
    let axiom  = Hashtbl.find r_a_h id in
    let _, _, (l, o) = Option.value_exn axiom ~here:_here_ in
    match Hashtbl.find r_a_occ_h (id, dvars) with
    | Some substitutions ->
      let f substitution =
        let bindings =
          let f x = `Int x in
          List.map substitution ~f in
        let f (l, s) (c, m) =
          let m = Conv.term_of_t m ~bindings in
          let v, o = Lazy.force (S.ovar_of_term r_ctx m)
          and f v = (c, v) :: l
          and default = l in
          Option.value_map v ~f ~default, Int63.(s + c * o)
        and init = [], o in
        List.fold_left l ~f ~init in
      List.map substitutions ~f
    | None ->
      []

  let assert_axiom ({r_lt_ctx; r_a_h} as r) axiom =
    let id = Lt.assert_axiom r_lt_ctx (instantiate r) in
    Hashtbl.replace r_a_h id axiom;
    register_axiom_terms r id axiom

  let solve ({r_ctx; r_lt_ctx; r_occ_h; r_q} as r) =
    Dequeue.iter r_q ~f:(register_apps_formula r);
    Dequeue.iter r_q ~f:(S.assert_formula r_ctx);
    register_all_axiom_terms r;
    let f = get_cuts r_occ_h in
    let id = Lt.assert_axiom r_lt_ctx f in
    register_diffs r id;
    S.solve r_ctx

  let add_objective {r_ctx} = S.add_objective r_ctx

  let deref_int {r_ctx} = S.deref_int r_ctx

  let deref_bool {r_ctx} = S.deref_bool r_ctx

  let write_bg_ctx {r_ctx} = S.write_bg_ctx r_ctx

end
