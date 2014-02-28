open Core.Std
open Logic

module Make (Imt : Imt_intf.S_with_cut_gen) (I : Id.S) = struct

  module Lt = Lt.Make(Imt)

  module Imt' = Imt.F(Lt)

  module S = Solver.Make(Imt')(I)
  
  let make_ctx () =
    S.make_ctx (Imt'.make_ctx (Lt.make_ctx ()))

  let assert_axiom = Lt.assert_axiom

  let assert_instance = Lt.assert_instance

  type c = I.c

  type mono_id = (I.c, int -> int) Id.t

  type int_term = (I.c, int) M.t

  type formula = I.c A.t Formula.t

  type app = int_term * int_term

  type ovar = Imt.ivar option Terminology.offset
  (* with compare, sexp_of *)

  type ovar_pair = ovar * ovar
  (* with compare, sexp_of *)

  (* FIXME : monomorphic tables / sets *)

  type ctx = {
    r_ctx      :  S.ctx;
    r_lt_ctx   :  Lt.ctx;
    r_imt_ctx  :  Imt'.ctx;
    r_f_h      :  (mono_id, app Hash_set.t) Hashtbl.t;
    r_occ_h    :  (Imt.Dvars.t, (ovar * ovar) list) Hashtbl.t;
    r_q        :  formula Dequeue.t
  }

  let make_ctx () =
    let r_f_h      =  Hashtbl.Poly.create () ~size:128
    and r_lt_ctx   =  Lt.make_ctx () in
    let r_imt_ctx  =  Imt'.make_ctx r_lt_ctx in
    let r_ctx      =  S.make_ctx r_imt_ctx
    and r_occ_h    = 
      Hashtbl.create () ~size:2048 ~hashable:Imt.Dvars.hashable
    and r_q        =  Dequeue.create () in
    {r_ctx; r_lt_ctx; r_imt_ctx; r_f_h; r_occ_h; r_q}

  let mono_increasing {r_f_h} (f : (I.c, int -> int) Id.t) =
    let default () = Hash_set.Poly.create () ~size:128 in
    ignore (Hashtbl.find_or_add r_f_h f ~default)

  let assert_formula {r_ctx; r_q} g =
    Dequeue.enqueue_back r_q g

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
          (match Hashtbl.find r_f_h id with
          | Some h ->
            Hash_set.add h (a, a')
          | _ ->
            f a)
        | _ ->
          f a)
      | M.M_App (a, b)->
        f a; f b in
    let f a ~polarity =
      match a with
      | A.A_Bool m ->
        f m
      | A.A_Le m | A.A_Eq m ->
        f m
    and polarity = `Both in
    Formula.iter_non_atomic g ~f ~polarity

  let register_diffs
      {r_ctx; r_imt_ctx; r_lt_ctx; r_f_h; r_occ_h}
      axiom_id =
    let f ~key ~data =
      let f = Fn.compose Lazy.force (S.ovar_of_term r_ctx) in
      let f (v1, v2) = f v1, f v2 in
      (* FIXME : avoid conversion *)
      let data = Hash_set.to_list data in
      let data = List.map data ~f in
      let f (ov1, ovr1) (ov2, ovr2) =
        let dv = Imt.Dvars.create_dvar r_imt_ctx ov1 ov2 in
        Hashtbl.add_multi r_occ_h dv (ovr1, ovr2);
        Lt.assert_instance r_lt_ctx axiom_id [dv];
        let dv = Imt.Dvars.create_dvar r_imt_ctx ov2 ov1 in
        Hashtbl.add_multi r_occ_h dv (ovr2, ovr1);
        Lt.assert_instance r_lt_ctx axiom_id [dv] in
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
        List.map l ~f:(fun (ovr1, ovr2) -> get_cut ovr1 ovr2)
      | None ->
        [])
    | _ ->
      []

  let solve ({r_ctx; r_lt_ctx; r_occ_h; r_q} as r) =
    Dequeue.iter r_q ~f:(register_apps_formula r);
    Dequeue.iter r_q ~f:(S.assert_formula r_ctx);
    let f = get_cuts r_occ_h in
    let axiom_id = Lt.assert_axiom r_lt_ctx f in
    register_diffs r axiom_id;
    S.solve r_ctx

  let add_objective {r_ctx} = S.add_objective r_ctx

  let deref_int {r_ctx} = S.deref_int r_ctx

  let deref_bool {r_ctx} = S.deref_bool r_ctx

  let write_bg_ctx {r_ctx} = S.write_bg_ctx r_ctx

end
