open Core.Std
open Logic

module Make (Imt : Imt_intf.S_with_cut_gen) (I : Id.S) = struct
  
  module Matching = Flat.Matching(M)

  module Conv = Flat.Conv(I)(M)

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

  type iexpr = Imt.ivar Terminology.iexpr
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
    r_a_h       :  (Lt.axiom_id, c Axiom.Flat.t) Hashtbl.t;
    r_a_patt_h  :
      (c Id.Box_arrow.t, (Lt.axiom_id * c Flat.Box.t) list)
      Hashtbl.t;
    r_a_bind_h  :
      (Lt.axiom_id,
       ((c, int) Id.t, (c, int) M.t list) Hashtbl.t)
      Hashtbl.t;
    r_a_occ_h   :  (aocc, binding list list) Hashtbl.t;
    r_dvars_h   :  (ovov, Imt.Dvars.t) Hashtbl.t;
    r_q         :  formula Dequeue.t
  }

  let make_ctx () =
    let r_lt_ctx    =  Lt.make_ctx () in
    let r_imt_ctx   =  Imt'.make_ctx r_lt_ctx in
    let r_ctx       =  S.make_ctx r_imt_ctx
    and r_a_h       =  Hashtbl.Poly.create () ~size:32
    and r_a_patt_h  =  Hashtbl.Poly.create () ~size:1024
    and r_a_bind_h  =  Hashtbl.Poly.create () ~size:4096
    and r_a_occ_h   =
      Hashtbl.create () ~size:4096 ~hashable:hashable_aocc;
    and r_dvars_h   =
      Hashtbl.create () ~size:2048 ~hashable:hashable_ovov
    and r_q         =  Dequeue.create () in
    {r_ctx; r_lt_ctx; r_imt_ctx;
     r_a_h; r_a_patt_h; r_a_bind_h; r_a_occ_h;
     r_dvars_h; r_q}

  let assert_formula {r_q} =
    Dequeue.enqueue_back r_q

  let bind_for_axiom {r_a_h; r_a_bind_h} axiom_id key data =
    let axiom = Hashtbl.find r_a_h axiom_id in
    let q, _, _ = Option.value_exn axiom ~here:_here_ in
    if List.exists q ~f:((=) key) then
      let h =
        let default () = Hashtbl.Poly.create () ~size:128 in
        Hashtbl.find_or_add r_a_bind_h axiom_id ~default
      and f x =
        match x with
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

  let register_app_for_axioms ({r_a_patt_h} as r) (m : (c, int) M.t) =
    match m with
    | M.M_App (a, b) ->
      Option.value_exn ~here:_here_ (M.fun_id_of_app m) |>
          Hashtbl.find r_a_patt_h |>
              let f (axiom_id, Flat.Box.Box pattern) =
                let f =
                  let f = function
                    | `Bool (_, _) ->
                      (* FIXME: let's deal with integers first *)
                      raise (Unreachable.Exn _here_)
                    | `Int (id, m) ->
                      bind_for_axiom r axiom_id id m in
                  List.iter ~f in
                Matching.do_for_match m ~pattern ~f in
              let f = List.iter ~f in
              Option.iter ~f
    | _ ->
      raise (Unreachable.Exn _here_)

  let rec iter_substitutions r axiom_id h q ~f ~bound =
    match q with
    | a :: d ->
      Hashtbl.find h a |>
          (let f =
             let f m =
               let bound = (a, m) :: bound in
               iter_substitutions r axiom_id h d ~f ~bound in
             List.iter ~f in
           Option.iter ~f)
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

  let instantiate {r_ctx} (l, o) ~bindings =
    let f (l, s) (c, m) =
      Conv.term_of_t m ~bindings |>
          S.ovar_of_term r_ctx |>
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

  let register_all_axiom_terms
      ({r_ctx; r_lt_ctx; r_a_h; r_a_occ_h} as r) =
    let f ~key ~data:(q, l, c) =
      let f s =
        let bindings = bindings_of_substitution s in
        let f (a, b) =
          let f x =
            instantiate r ~bindings x |> S.ovar_of_sum r_ctx in
          get_dvar r (f a) (f b) in
        let dvars = List.map l ~f in
        Lt.assert_instance r_lt_ctx key dvars;
        Hashtbl.add_multi r_a_occ_h (key, dvars) s in
      iter_substitutions r key ~f in
    Hashtbl.iter r_a_h ~f
  
  let rec register_apps_formula ({r_ctx} as r) =
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
    Formula.iter_atoms ~f ~polarity

  let register_axiom_terms {r_a_patt_h} id axiom =
    let open Flat in
    let f = function
      | M_Var _ ->
        ()
      | M_App (_, _) as m ->
        let key = Option.value_exn (fun_id_of_app m) ~here:_here_
        and data = id, Flat.Box.Box m in
        Hashtbl.add_multi r_a_patt_h ~key ~data in
    Axiom.Flat.iter_subterms axiom ~f

  let instantiate ({r_a_h; r_a_occ_h} as r) id dvars =
    let axiom  = Hashtbl.find r_a_h id in
    let _, _, cut = Option.value_exn axiom ~here:_here_ in
    let open List in
    Hashtbl.find r_a_occ_h (id, dvars) |>
        Option.value ~default:[] >>|
            (fun s ->
              let bindings = bindings_of_substitution s in
              instantiate r cut ~bindings)

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

  let flatten_axiom (q, (l, (c1, c2))) =
    let open Option in (
      let f acc (m1, m2) =
        acc >>= (fun (l, bindings) ->
          Conv.sum_of_term m1 ~bindings >>= (fun (s1, bindings) ->
            Conv.sum_of_term m2 ~bindings >>| (fun (s2, bindings) ->
              (s1, s2) :: l, bindings)))
      and init = Some ([], []) in
      List.fold_left l ~init ~f) >>= (fun (l, bindings) ->
        M.(c1 - c2) |>
            cut_of_term ~bindings >>| (fun (cut, bindings) ->
              let q =
                let f = Tuple.T2.get1 in
                List.rev_map_append bindings q ~f
              and h =
                let f acc (id, def) =
                  let e = Int63.([one, Flat.M_Var id], zero) in
                  (e, def) :: (def, e) :: acc
                and init = l in
                List.fold_left bindings ~f ~init in
              q, h, cut))

  let assert_axiom ({r_lt_ctx; r_a_h} as r) axiom =
    let f axiom =
      let id = instantiate r |> Lt.assert_axiom r_lt_ctx in
      Hashtbl.replace r_a_h id axiom;
      register_axiom_terms r id axiom;
      `Ok
    and default = `Unsupported in
    Option.value_map (flatten_axiom axiom) ~f ~default

  let solve ({r_ctx; r_lt_ctx; r_q} as r) =
    (let f = register_apps_formula r in
     Dequeue.iter r_q ~f);
    (let f = S.assert_formula r_ctx in
     Dequeue.iter r_q ~f);
    register_all_axiom_terms r;
    S.solve r_ctx

  let add_objective {r_ctx} = S.add_objective r_ctx

  let deref_int {r_ctx} = S.deref_int r_ctx

  let deref_bool {r_ctx} = S.deref_bool r_ctx

  let write_bg_ctx {r_ctx} = S.write_bg_ctx r_ctx

end
