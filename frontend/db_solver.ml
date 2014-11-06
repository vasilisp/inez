open Core.Std
open Db_logic
open Terminology
open Core.Int_replace_polymorphic_compare

module Make (Imt : Imt_intf.S_with_dp) (I : Id.S) = struct

  module Dp = Mem.Make(Imt)

  module Smt = Smtlib_printer.Make(I)

  module Imt' = Imt.F(Dp)

  module S' = Solver.Make(Imt')(I)

  module C =  Logic.Make_term_conv(M)(Logic.M)

  type ibentry =
    (S'.ovar Lazy.t, S'.xvar Lazy.t) ibeither

  type table_lazy = S'.ovar list list Lazy.t

  type in_constraint_lazy = ibentry list * table_lazy

  type d_boxed = DBox : (I.c, 's) R.t list -> d_boxed

  type mode = [`Eager | `Smt_out | `Lazy]

  type bool_id = (I.c, bool) Id.t

  let hashable_bool_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Id.compare I.compare_c Bool.compare;
    sexp_of_t = Id.sexp_of_t I.sexp_of_c Bool.sexp_of_t
  }

  type ctx = {
    r_ctx           :  S'.ctx;
    r_bg_ctx        :  Imt'.ctx;
    r_theory_ctx    :  Dp.ctx;
    r_mode          :  mode;
    r_table_lazy_h  :  (d_boxed, table_lazy) Hashtbl.t;
    r_in_m          :  (bool_id, in_constraint_lazy list) Hashtbl.t;
    r_smtlib_ctx    :  Smt.ctx option;
  }

  let make_ctx r_mode =
    let r_theory_ctx = Dp.make_ctx () in
    let r_bg_ctx = Imt'.make_ctx r_theory_ctx in {
      r_ctx =
        S'.make_ctx r_bg_ctx;
      r_bg_ctx;
      r_theory_ctx;
      r_mode;
      (* TODO : monomorphic hashtable *)
      r_table_lazy_h =
        Hashtbl.Poly.create () ~size:32;
      r_in_m = 
        Hashtbl.create () ~size:10240 ~hashable:hashable_bool_id;
      r_smtlib_ctx =
        match r_mode with
        | `Smt_out ->
          Some (Smt.make_ctx ())
        | _ ->
          None
    }

  let rec get_dummy_row :
  type s . s S.t -> (I.c, s) R.t =
    function
    | S.S_Int ->
      R.R_Int (M.M_Var (I.gen_id Type.Y_Int))
    | S.S_Bool ->
      R.R_Bool (M.M_Var (I.gen_id Type.Y_Bool))
    | S.S_Pair (a, b) ->
      R.R_Pair (get_dummy_row a, get_dummy_row b)

  let rec get_dummy_row_db :
  type s . (I.c, s) D.t -> (I.c, s) R.t =
    function
    | D.D_Rel (s, _) ->
      get_dummy_row s
    | D.D_Input (s, _) ->
      get_dummy_row s
    | D.D_Cross (a, b) ->
      R.R_Pair (get_dummy_row_db a, get_dummy_row_db b)
    | D.D_Sel (a, _) ->
      get_dummy_row_db a
  
  let rec get_symbolic_row :
  type s . s S.t -> (I.c, s) R.t =
    function
    | S.S_Int ->
      R.R_Int (M.M_Var (I.gen_id Type.Y_Int))
    | S.S_Bool ->
      R.R_Bool (M.M_Var (I.gen_id Type.Y_Bool))
    | S.S_Pair (a, b) ->
      R.R_Pair (get_symbolic_row a, get_symbolic_row b)

  let rec get_symbolic_row_db :
  type s . (I.c, s) D.t -> (I.c, s) R.t =
    function
    | D.D_Rel (s, _) ->
      get_symbolic_row s
    | D.D_Input (s, _) ->
      get_symbolic_row s
    | D.D_Cross (a, b) ->
      R.R_Pair (get_symbolic_row_db a, get_symbolic_row_db b)
    | D.D_Sel (a, _) ->
      get_symbolic_row_db a

  let force_row {r_ctx} =
    List.map
      ~f:(function
      | H_Int i ->
        Lazy.force i
      | H_Bool b ->
        (match Lazy.force b with
        | S_Pos (Some b) ->
          Some (Imt'.ivar_of_bvar b), Int63.zero
        | S_Neg (Some b) ->
          Some (Imt'.ivar_of_bvar (S'.negate_bvar r_ctx b)),
          Int63.zero
        | S_Pos None ->
          None, Int63.one
        | S_Neg None ->
          None, Int63.zero))

  type polarity = [ `Positive | `Negative | `Both ]

  let negate_polarity = function
    | `Positive -> `Negative
    | `Negative -> `Positive
    | `Both -> `Both

  let rec in_fragment_row :
  type s . (I.c, s) R.t -> bool =
    let under_forall = false in
    function
    | R.R_Int m ->
      in_fragment_term ~under_forall m
    | R.R_Bool b ->
      in_fragment_term ~under_forall b
    | R.R_Pair (a, b) ->
      in_fragment_row a && in_fragment_row b

  and in_fragment_db :
  type s . under_forall:bool -> polarity:polarity ->
    (I.c, s) D.t -> bool =
    fun ~under_forall ~polarity -> function
    | D.D_Rel (s, f) ->
      (* FIXME: looks fine, but think about it again *)
      not under_forall &&
        let polarity = `Positive
        and row = get_dummy_row s |> f in
        in_fragment row ~under_forall ~polarity
    | D.D_Input (_, l) ->
      List.for_all l ~f:in_fragment_row
    | D.D_Cross (a, b) when under_forall ->
      false
    | D.D_Cross (a, b) ->
      in_fragment_db ~under_forall ~polarity a &&
        in_fragment_db ~under_forall ~polarity b
    | D.D_Sel (a, f) ->
      in_fragment_db ~under_forall ~polarity a &&
        let g = f (get_dummy_row_db a) in
        in_fragment ~under_forall ~polarity g

  and in_fragment_term :
  type s . under_forall:bool -> (I.c, s) M.t -> bool =
    fun ~under_forall -> function
    | M.M_Int _ ->
      true
    | M.M_Var _ ->
      true
    | M.M_Bool g ->
      in_fragment ~under_forall ~polarity:`Both g
    | M.M_Sum (a, b) ->
      in_fragment_term ~under_forall a &&
        in_fragment_term ~under_forall b
    | M.M_Prod (_, a) ->
      in_fragment_term ~under_forall a
    | M.M_Ite (q, a, b) ->
      in_fragment ~under_forall ~polarity:`Both q &&
        in_fragment_term ~under_forall a &&
        in_fragment_term ~under_forall b
    | M.M_App (a, b) ->
      in_fragment_term ~under_forall a &&
        in_fragment_term ~under_forall b

  and in_fragment ~under_forall ~polarity =
    function
    | Formula.F_True ->
      true
    | Formula.F_Not g ->
      let polarity = negate_polarity polarity in
      in_fragment ~under_forall ~polarity g
    | Formula.F_And (g, h) ->
      in_fragment ~under_forall ~polarity g &&
        in_fragment ~under_forall ~polarity h
    | Formula.F_Ite (q, g, h) ->
      in_fragment ~under_forall ~polarity:`Both q &&
        in_fragment ~under_forall ~polarity g &&
        in_fragment ~under_forall ~polarity h
    | Formula.F_Atom (A.A_Exists d) ->
      (match polarity, under_forall with
      | `Positive, _ ->
        in_fragment_db ~under_forall:false ~polarity d
      | _, false ->
        in_fragment_db ~under_forall:true ~polarity d
      | _, true ->
        false)
    | Formula.F_Atom (A.A_Bool (M.M_Bool g)) ->
      in_fragment ~under_forall ~polarity g
    | Formula.F_Atom (A.A_Bool b) ->
      in_fragment_term ~under_forall b
    | Formula.F_Atom (A.A_Le m | A.A_Eq m) ->
      in_fragment_term ~under_forall m

  let register_membership_bulk   {r_in_m} b l =
    Hashtbl.change r_in_m b
      (function
      | Some l1 -> Some (List.append l l1)
      | None -> Some l)

  let fv = {Id.f_id = Fn.id}

  let rec path_and_data_of_db :
  type s . ?acc:(((I.c, s) R.t -> I.c A.t Formula.t) list) ->
    (I.c, s) D.t ->
    (((I.c, s) R.t -> I.c A.t Formula.t) list) *
      (I.c, s) R.t list option =
    fun ?acc:(acc = []) -> function
    | D.D_Rel (_, f) ->
      f :: acc, None
    | D.D_Input (_, d) ->
      acc, Some d
    | D.D_Cross (_, _) ->
      raise (Unreachable.Exn _here_)
    | D.D_Sel (d, f) ->
      let acc = f :: acc in
      path_and_data_of_db d ~acc 

  let rec list_of_row_aux :
  type s. ibentry list -> ctx -> (I.c, s) R.t ->
    ibentry list =
    fun acc ({r_ctx} as x) r ->
      let f = purify_atom x in
      match r with
      | R.R_Int m ->
        let m = C.map_non_atomic m ~f ~fv in
        let m = S'.ovar_of_term r_ctx m in
        H_Int m :: acc
      | R.R_Bool m ->
        let m = C.map_non_atomic m ~f ~fv in
        let m = S'.xvar_of_term r_ctx m in
        H_Bool m :: acc
      | R.R_Pair (r1, r2) ->
        let acc = list_of_row_aux acc x r1 in
        list_of_row_aux acc x r2

  and list_of_row :
  type s. ctx -> (I.c, s) R.t -> ibentry list =
    fun x r -> List.rev (list_of_row_aux [] x r)

  and table_lazy_of_db :
  type s . ctx -> (I.c, s) R.t list -> table_lazy =
    fun ({r_table_lazy_h} as x) l ->
      let default () =
        let ll = List.map l ~f:(list_of_row x) in
        lazy (List.map ll ~f:(force_row x)) in
      Hashtbl.find_or_add r_table_lazy_h (DBox l) ~default

  and purify_membership :
  type s . ?acc:(in_constraint_lazy list) -> ctx ->
    (I.c, s) D.t -> (I.c, s) R.t ->
    in_constraint_lazy list * I.c Logic.A.t Formula.t =
    fun ?acc:(acc = []) x d r ->
      match d, r with
      | D.D_Rel (_, f), r ->
        acc, purify_formula x (f r) ~polarity:`Positive
      | D.D_Input (_, l), _ ->
        let ll = table_lazy_of_db x l
        and rl = list_of_row x r in
        (rl, ll) :: acc, Formula.true'
      | D.D_Cross (d1, d2), R.R_Pair (r1, r2) ->
        let acc, g1 = purify_membership ~acc x d1 r1 in
        let acc, g2 = purify_membership ~acc x d2 r2 in
        acc, Formula.(g1 && g2)
      | D.D_Sel (d, f), _ ->
        let g1 = purify_formula x (f r) ~polarity:`Positive in
        let acc, g2 = purify_membership ~acc x d r in
        acc, Formula.(g1 && g2)

  and columnwise_equal :
  type s. ctx -> (I.c, s) R.t -> (I.c, s) R.t ->
    I.c Logic.A.t Formula.t =
    fun x r1 r2 ->
      let f = purify_atom x in
      match r1, r2 with
      | R.R_Int m1, R.R_Int m2 ->
        let m1 = C.map_non_atomic m1 ~f ~fv
        and m2 = C.map_non_atomic m2 ~f ~fv in
        Logic.Ops.(m1 = m2)
      | R.R_Bool b1, R.R_Bool b2 ->
        let b1 = C.map_non_atomic b1 ~f ~fv
        and b2 = C.map_non_atomic b2 ~f ~fv in
        let b1 = Formula.F_Atom (Logic.A.A_Bool b1)
        and b2 = Formula.F_Atom (Logic.A.A_Bool b2) in
        Formula.((b1 => b2) && (b2 => b1))
      | R.R_Pair (r11, r12), R.R_Pair (r21, r22) ->
        Formula.(&&)
          (columnwise_equal x r11 r21)
          (columnwise_equal x r12 r22)

  and purify_membership_eager :
  type s. ctx -> (I.c, s) D.t -> (I.c, s) R.t ->
    I.c Logic.A.t Formula.t =
    fun x d r ->
      match d, r with
      | D.D_Rel (_, f), r ->
        purify_formula x (f r) ~polarity:`Positive
      | D.D_Input (_, l), r ->
        Formula.exists l ~f:(columnwise_equal x r)
      | D.D_Cross (d1, d2), R.R_Pair (r1, r2) ->
        Formula.(&&)
          (purify_membership_eager x d1 r1)
          (purify_membership_eager x d2 r2)
      | D.D_Sel (d, f), r ->
        Formula.(&&)
          (purify_formula x (f r) ~polarity:`Positive)
          (purify_membership_eager x d r)

  and purify_atom :
  ctx -> I.c A.t -> polarity:polarity -> I.c Logic.A.t Formula.t = 
    fun ({r_ctx; r_mode} as x) a ~polarity ->
      match a, polarity, r_mode with
      | A.A_Exists d, `Positive, (`Smt_out | `Eager) ->
        let r = get_symbolic_row_db d in
        purify_membership_eager x d r
      | A.A_Exists d, `Positive, _ ->
        let l, g =
          let r = get_symbolic_row_db d in
          purify_membership x d r
        and b = I.gen_id Type.Y_Bool in
        register_membership_bulk x b l;
        Formula.(&&) g
          (Formula.F_Atom
             (Logic.A.A_Bool
                (Logic.M.M_Var b)))
      | A.A_Exists d, _, _ ->
        let l, d = path_and_data_of_db d in
        let f r =
          let f g = purify_formula x (g r) ~polarity in 
          Formula.forall l ~f
        and d = Option.value_exn ~here:_here_ d in
        Formula.exists d ~f
      | A.A_Bool b, _, _ ->
        Formula.F_Atom
          (Logic.A.A_Bool
             (C.map_non_atomic b ~f:(purify_atom x) ~fv))
      | A.A_Le s, _, _ ->
        Formula.F_Atom
          (Logic.A.A_Le
             (C.map_non_atomic s ~f:(purify_atom x) ~fv))
      | A.A_Eq s, _, _ ->
        Formula.F_Atom
          (Logic.A.A_Eq
             (C.map_non_atomic s ~f:(purify_atom x) ~fv))

  and purify_formula x ~polarity =
    Formula.map_non_atomic ~f:(purify_atom x) ~polarity

  let purify_formula_top x g =
    if in_fragment ~under_forall:false ~polarity:`Positive g then
      Some (purify_formula x g  ~polarity:`Positive)
    else
      None

  let assert_formula {r_mode; r_ctx; r_smtlib_ctx} g =
    match r_mode with
    | `Smt_out ->
      let r_smtlib_ctx = Option.value_exn ~here:_here_ r_smtlib_ctx in
      Smt.assert_formula r_smtlib_ctx g
    | _ ->
      S'.assert_formula r_ctx g

  let assert_formula ({r_ctx; r_mode} as x) g =
    match purify_formula_top x g with
    | Some g ->
      assert_formula x g; `Ok
    | None ->
      `Out_of_fragment

  let name_diff r v1 v2 =
    let v = Imt'.new_ivar r in
    Int63.(Imt'.add_eq r [minus_one, v1; one, v2; one, v] zero);
    v

  let solve ({r_ctx; r_bg_ctx; r_theory_ctx; r_in_m; r_mode;
              r_smtlib_ctx} as x) =
    match r_mode with
    | `Lazy ->
      let f ~key ~data =
        let v = S'.bvar_of_id r_ctx key
        and fd = name_diff r_bg_ctx
        and frv = Imt'.register_ivar r_bg_ctx in
        Imt'.register_bvar r_bg_ctx v;
        let f (e, l) =
          let e =
            let e = force_row x e
            and f = function
              | Some v, _ ->
                Imt'.register_ivar r_bg_ctx v
              | _ ->
                () in
            List.iter e ~f;
            e
          and l = Lazy.force l in
          Dp.assert_membership r_theory_ctx v e l ~fd ~frv in
        List.iter data ~f in
      Hashtbl.iter r_in_m ~f;
      let r = S'.solve r_ctx in
      if !Sys.interactive then Dp.print_stats r_theory_ctx;
      r
    | `Eager when Hashtbl.is_empty r_in_m ->
      S'.solve r_ctx
    | `Eager ->
      raise (Unreachable.Exn _here_)
    | `Smt_out ->
      let r_smtlib_ctx = Option.value_exn ~here:_here_ r_smtlib_ctx in
      Smt.solve r_smtlib_ctx;
      R_Unknown

  let add_objective ({r_ctx; r_mode} as x) o =
    match r_mode with
    | `Smt_out ->
      `Out_of_fragment
    | _ when in_fragment_term ~under_forall:false o ->
      let o = C.map_non_atomic o ~f:(purify_atom x) ~fv in
      S'.add_objective r_ctx o
    | _ ->
      `Out_of_fragment
 
  let write_bg_ctx {r_ctx} =
    S'.write_bg_ctx r_ctx

  let deref_int {r_ctx} i =
    S'.deref_int r_ctx i

  let deref_bool {r_ctx} i =
    S'.deref_bool r_ctx i

end
