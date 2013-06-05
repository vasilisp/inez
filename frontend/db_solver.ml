open Core.Std
open Db_lang_abstract
open Terminology

module Make (Imt : Imt_intf.S_with_dp) (I : Lang_ids.S) = struct

  type int_id = (I.c, int) Lang_ids.t
  
  type bool_id = (I.c, bool) Lang_ids.t

  let hashable_int_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Lang_ids.compare I.compare_c Int.compare;
    sexp_of_t = Lang_ids.sexp_of_t I.sexp_of_c Int.sexp_of_t
  }

  let hashable_bool_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Lang_ids.compare I.compare_c Bool.compare;
    sexp_of_t = Lang_ids.sexp_of_t I.sexp_of_c Bool.sexp_of_t
  }

  let hashable_ivar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Imt.compare_ivar;
    sexp_of_t = Imt.sexp_of_ivar
  }

  let hashable_bvar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Imt.compare_bvar;
    sexp_of_t = Imt.sexp_of_bvar
  }

  module Lb = struct
    let (<=) lb lb' =
      match lb, lb' with
      | Some lb, Some lb' ->
        Int63.(lb <= lb')
      | Some lb, None ->
        false
      | None, _ ->
        true
  end

  module Ub = struct
    let (<=) ub ub' =
      match ub, ub' with
      | Some ub, Some ub' ->
        Int63.(ub <= ub')
      | Some ub, None ->
        true
      | None, _ ->
        false
  end
  
  module Lb_ub = struct
    let (<=) lb ub =
      match lb, ub with
      | Some lb, Some ub ->
        Int63.(lb <= ub)
      | Some lb, None ->
        true
      | None, _ ->
        true
  end

  module Ub_lb = struct
    let (<=) a b = Lb_ub.(b <= a)
  end

  module Zom = struct

    type 'a t = Z0 | Z1 of 'a | Zn

    let update z x ~equal =
      match z with
      | Z0 ->
        Z1 x
      | Z1 x' when equal x x' ->
        z
      | _ ->
        Zn

  end

  (* We provide a theory solver (module [D]) and instantiate BC(T)
     accordingly ([Imt.F(D)]). *)

  module Theory_solver = struct

    type elmt = Imt.ivar option offset
    with compare, sexp_of

    type row = elmt array
    with compare, sexp_of

    type db = row list
    with compare, sexp_of

    let hashable_db = {
      Hashtbl.Hashable.
      hash = Hashtbl.hash;
      compare = compare_db;
      sexp_of_t = sexp_of_db
    }

    type ipair = Imt.ivar * Imt.ivar
    with compare, sexp_of

    let hashable_ipair = {
      Hashtbl.Hashable.
      hash = Hashtbl.hash;
      compare = compare_ipair;
      sexp_of_t = sexp_of_ipair
    }

    type index = row Int63.Map.t * row list

    type occ = row * index * int

    let dequeue_exists d ~f =
      let back = Dequeue.back_index d in
      let rec g i =
        if i <= back then
          if f (Dequeue.get_exn d i) then
            true
          else
            g (i + 1)
        else
          false in
      g (Dequeue.front_index d)

    let dequeue_for_all d ~f =
      not (dequeue_exists d ~f:(Fn.non f))

    type ctx = {
      r_idb_h   :  (db, index) Hashtbl.t;
      r_bvar_d  :  Imt.bvar option Dequeue.t;
      r_diff_h  :  (ipair, Imt.ivar) Hashtbl.t;
      r_occ_h   :  (Imt.bvar, occ list) Hashtbl.t
    }

    let make_ctx () = {
      r_idb_h =
        Hashtbl.create () ~size:64 ~hashable:hashable_db;
      r_bvar_d =
        Dequeue.create () ~dummy:None;
      r_diff_h =
        Hashtbl.create () ~size:1024 ~hashable:hashable_ipair;
      r_occ_h =
        Hashtbl.create () ~size:1024 ~hashable:hashable_bvar;
    }

    let index_of_db_dimension l i =
      List.fold_left l
        ~init:(Int63.Map.empty, [])
        ~f:(fun (accm, accl) data ->
          match Array.get data i with
          | None, key ->
            Map.add accm ~key ~data, accl
          | _ ->
            accm, data :: accl)

    let index_of_db {r_idb_h} d i =
      Hashtbl.find_or_add r_idb_h d
        ~default:(fun () -> index_of_db_dimension d i)

    let bvar_in_dequeue d v =
      let f x y = Imt.compare_bvar x y = 0 in
      let f = Option.equal f (Some v) in
      dequeue_exists d ~f

    let rec ivar_of_diff ({r_diff_h} as r) v1 v2 ~fd =
      if compare v1 v2 > 0 then
        ivar_of_diff r v2 v1 ~fd
      else if compare v1 v2 = 0 then
        None
      else
        let default () = fd v1 v2 in
        Some (Hashtbl.find_or_add r_diff_h (v1, v2) ~default)

    let register_diffs r row1 row2 ~fd =
      Array.iter2_exn row1 row2
        ~f:(fun (v1, _) (v2, _) ->
          match v1, v2 with
          | Some v1, Some v2 when not (compare v1 v2 = 0) ->
            ignore (ivar_of_diff r v1 v2 ~fd)
          | _, _ ->
            ())

    let assert_membership
        ({r_bvar_d; r_occ_h} as r) b e l ~fd =
      let e = Array.of_list e
      and l = List.map l ~f:Array.of_list in
      List.iter l ~f:(register_diffs r e ~fd);
      let index = index_of_db r l 0 in
      if not (bvar_in_dequeue r_bvar_d b) then
        Dequeue.push_back r_bvar_d (Some b);
      Hashtbl.add_multi r_occ_h b (e, index, 0)

    module F

      (S : Imt_intf.S_dp_access
       with type ivar = Imt.ivar
       and type bvar = Imt.bvar) =

    struct

      type 'a folded =
        row ->
        bounds:(Int63.t option * Int63.t option) array ->
        acc:'a -> 'a

      type 'a mapped =
        row -> bounds:(Int63.t option * Int63.t option) array -> 'a

      let lb_of_ovar r' = function
        | Some v, o ->
          Option.(S.get_lb_local r' v >>| Int63.(+) o)
        | None, o ->
          Some o

      let ub_of_ovar r' = function
        | Some v, o ->
          Option.(S.get_ub_local r' v >>| Int63.(+) o)
        | None, o ->
          Some o

      let bounds_of_row r' =
        let f ov = lb_of_ovar r' ov, ub_of_ovar r' ov in
        Array.map ~f

      let bounds_within_for_dim (lb, ub) (lb', ub') =
        (Lb.(lb' <= lb) && Lb_ub.(lb <= ub')) ||
          (Lb_ub.(lb' <= ub) && Ub.(ub <= ub'))

      let get_diff_lb {r_diff_h} r' v1 v2 =
        if compare v1 v2 = 0 then
          Some Int63.zero
        else if compare v1 v2 > 0 then
          let open Option in
          Hashtbl.find r_diff_h (v1, v2) >>= S.get_lb_local r'
        else
          let open Option in
          Hashtbl.find r_diff_h (v2, v1) >>=
            S.get_ub_local r' >>| Int63.neg

      let get_diff_ub {r_diff_h} r' v1 v2 =
        if compare v1 v2 = 0 then
          Some Int63.zero
        else if compare v1 v2 > 0 then
          let open Option in
          Hashtbl.find r_diff_h (v1, v2) >>= S.get_ub_local r'
        else
          let open Option in
          Hashtbl.find r_diff_h (v2, v1) >>=
            S.get_lb_local r' >>| Int63.neg

      let bounds_within a a' =
        Array.for_all2_exn a a' ~f:bounds_within_for_dim

      let maybe_equal_rows r r' row a row' a' =
        bounds_within a a' &&
          (Array.for_all2_exn row row'
             ~f:(fun ov1 ov2 ->
               match ov1, ov2 with
               | (Some v1, o1), (Some v2, o2) ->
                 let open Int63 in
                 let d = o2 - o1
                 and lb = get_diff_lb r r' v1 v2
                 and ub = get_diff_ub r r' v1 v2
                 and default = true in
                 Option.value_map lb ~f:((>=) d) ~default &&
                   Option.value_map ub ~f:((<=) d) ~default
               | _ ->
                 true))

      let fold_candidates ?map_only:(map_only = false)
          r r' (row, (m, l), i) ~init ~(f : 'a folded) =
        let a = bounds_of_row r' row in
        let f acc data =
          let bounds = bounds_of_row r' data  in
          if maybe_equal_rows r r' data bounds row a then
            f data ~bounds ~acc
          else
            acc in
        let f ~key ~data acc = f acc data
        and init =
          if map_only then
            init
          else
            List.fold_left l ~f ~init
        and lb = lb_of_ovar r' row.(i)
        and ub = ub_of_ovar r' row.(i) in
        let lb = Option.value lb ~default:Int63.min_value
        and ub = Option.value ub ~default:Int63.max_value in
        Map.fold_range_inclusive m ~min:lb ~max:ub ~init ~f

      let exists_candidate ?map_only:(map_only = false)
          r r' (row, (m, l), i) ~(f : bool mapped) =
        let a = bounds_of_row r' row in
        let f data =
          let bounds = bounds_of_row r' data  in
          maybe_equal_rows r r' data bounds row a &&
            f data ~bounds in
        let f ~key ~data acc = acc || f data
        and init = map_only || List.exists l ~f
        and lb = lb_of_ovar r' row.(i)
        and ub = ub_of_ovar r' row.(i) in
        let lb = Option.value lb ~default:Int63.min_value
        and ub = Option.value ub ~default:Int63.max_value in
        Map.fold_range_inclusive m ~min:lb ~max:ub ~init ~f

      let response_of_attempts a b =
        match a, b with
        | `Infeasible, _ | _, `Infeasible ->
          N_Unsat
        | `Tightened, _ | _, `Tightened ->
          N_Tightened
        | `Ok, `Ok ->
          N_Ok

      let maybe_upper_bound_ovar r r' ub (v, o) =
        match ub, v with
        | None, _ ->
          `Ok
        | Some ub, Some v ->
          S.set_ub_local r' v Int63.(ub - o)
        | Some ub, None ->
          if Int63.(ub >= o) then `Ok else `Infeasible

      let maybe_lower_bound_ovar r r' lb (v, o) =
        match lb, v with
        | None, _ ->
          `Ok
        | Some lb, Some v ->
          S.set_lb_local r' v Int63.(lb - o)
        | Some lb, None ->
          if Int63.(lb <= o) then `Ok else `Infeasible

      let occs_of_bvar {r_occ_h} v =
        Option.value (Hashtbl.find r_occ_h v) ~default:[]

      (* propagate *)

      let approx_candidates_folded r' row ~bounds ~acc:(a, z) =
        Array.iteri bounds
          ~f:(fun i (lb, ub) ->
            let lb', ub' = a.(i) in
            let lb_min = Option.map2 lb lb' ~f:Int63.min
            and ub_max = Option.map2 ub ub' ~f:Int63.max in
            a.(i) <- lb_min, ub_max);
        let equal (_, a) (_, a') =
          let eq1 = Option.equal Int63.equal in
          let equal = Tuple2.equal ~eq1 ~eq2:eq1 in
          Array.equal a a' ~equal in
        a, Zom.update z (row, bounds) ~equal

      let approx_candidates ?map_only:(map_only = false)
          r r' (row, _, _ as occ) =
        let n = Array.length row in
        let p = Some Int63.max_value, Some Int63.min_value in
        let init = Array.init ~f:(fun _ -> p) n, Zom.Z0 
        and f = approx_candidates_folded r' in
        fold_candidates r r' occ ~init ~f

      let fix_variable r v x =
        response_of_attempts
          (S.set_lb_local r v x)
          (S.set_ub_local r v x)

      let array_foldi_responses a ~f =
        let n = Array.length a in
        let rec g i acc =
          if i >= n then
            acc
          else
            match f i a.(i) with
            | N_Unsat ->
              N_Unsat
            | N_Tightened ->
              g (i + 1) N_Tightened
            | N_Ok ->
              g (i + 1) acc in
        g 0 N_Ok

      let dequeue_foldi_responses d ~f =
        let n = Dequeue.back_index d in
        let rec g i acc =
          if i > n then
            acc
          else
            match f i (Dequeue.get_exn d i) with
            | N_Unsat ->
              N_Unsat
            | N_Tightened ->
              g (i + 1) N_Tightened
            | N_Ok ->
              g (i + 1) acc in
        g (Dequeue.front_index d) N_Ok

      let list_foldi_responses l ~f =
        let rec g i l acc =
          match l with
          | a :: d ->
            (match f i a with
            | N_Unsat ->
              N_Unsat
            | N_Tightened ->
              g (i + 1) d N_Tightened
            | N_Ok ->
              g (i + 1) d acc)
          | [] ->
            acc in
        g 0 l N_Ok

      let assert_ovar_equal {r_diff_h} r' (v1, o1) (v2, o2) =
        let fb b = if b then N_Ok else N_Unsat
        and f v1 v2 x =
          let v = Hashtbl.find r_diff_h (v1, v2) in
          let v = Option.value_exn v ~here:_here_ in
          fix_variable r' v x
        and d = Int63.(o2 - o1) in
        match v1, v2 with
        | Some v1, Some v2 ->
          if Imt.compare_ivar v1 v2 = 0 then
            fb (Int63.equal o1 o2)
          else if Imt.compare_ivar v1 v2 > 0 then
            f v2 v1 d
          else
            f v1 v2 Int63.(neg d)
        | Some v1, None ->
          fix_variable r' v1 d
        | None, Some v2 ->
          fix_variable r' v2 Int63.(neg d)
        | None, None ->
          fb (Int63.equal o1 o2)

      let propagate_for_occ r r' (row, index, i as occ) =
        match approx_candidates r r' occ with
        | _, Zom.Z0 ->
          (* no candidates *)
          N_Unsat
        | _, Zom.Z1 (row2, _) ->
          (* propagate bounds *)
          let f i = assert_ovar_equal r r' row.(i) in
          array_foldi_responses row2 ~f
        | a, Zom.Zn ->
          array_foldi_responses a
            ~f:(fun i (lb, ub) ->
              let rl = maybe_lower_bound_ovar r r' lb row.(i)
              and ru = maybe_upper_bound_ovar r r' ub row.(i) in
              response_of_attempts rl ru)
              
      let propagate_for_bvar_aux r r' v =
        list_foldi_responses (occs_of_bvar r v)
          ~f:(fun _ -> propagate_for_occ r r')

      let propagate_for_bvar r r' v =
        Option.value_map (S.bderef_local r' v)
          ~f:(function true ->
            propagate_for_bvar_aux r r' v
          | false ->
            N_Ok)
          ~default:N_Ok
        
      let propagate ({r_bvar_d} as r) r' =
        dequeue_foldi_responses r_bvar_d
          ~f:(fun _ v ->
            let v = Option.value_exn v ~here:_here_ in
            propagate_for_bvar r r' v)

      (* check given solution *)
            
      let deref_ovar_sol r' sol = function
        | Some v, o ->
          Int63.(S.ideref_sol r' sol v + o)
        | None, o ->
          o

      let matches_row r' sol row_concrete row =
        Array.for_all2_exn row row_concrete
          ~f:(fun ov c -> Int63.equal (deref_ovar_sol r' sol ov) c)

      let exists_index (m, l) ~f ~min ~max =
        List.exists l ~f ||
          let f ~key ~data acc = acc || f data in
          Map.fold_range_inclusive m ~min ~max ~init:true ~f

      let check_for_occ r r' sol (row, index, i) =
        let row = Array.map row ~f:(deref_ovar_sol r' sol) in
        let f = matches_row r' sol row in
        exists_index index ~min:row.(i) ~max:row.(i) ~f

      let check_for_bvar ({r_occ_h} as r) r' sol v =
        not (S.bderef_sol r' sol v) ||
          List.for_all (occs_of_bvar r v) ~f:(check_for_occ r r' sol)

      let check ({r_bvar_d} as r) r' sol =
        let f = check_for_bvar r r' sol in
        let f = Fn.compose f (Option.value_exn ~here:_here_) in
        dequeue_for_all r_bvar_d ~f

      let ok_for_true = function
        | true  -> `Ok
        | false -> `Fail

      let bool_of_ok_or_fail = function
        | `Ok   -> true
        | `Fail -> false

      let branch_for_bvar r r' v ~f =
        match S.bderef_local r' v with
        | Some true ->
          List.exists (occs_of_bvar r v) ~f
        | _ ->
          false

      let branch {r_bvar_d; _} ~f =
        let f v = f (Option.value_exn v ~here:_here_) in
        dequeue_exists r_bvar_d ~f

      let branch_on_column r r' (lb, ub) ov =
        let lb = Option.value_exn lb ~here:_here_
        and ub = Option.value_exn ub ~here:_here_ in
        not (Int63.equal lb ub) &&
          match ov with
          | Some v, o ->
            let middle = Int63.((lb + ub) / (one + one) - o) in
            let middle = Int63.to_float middle +. 0.5 in
            bool_of_ok_or_fail (S.ibranch r' v middle)
          | None, _ ->
            false

      let branch0_for_occ ?any:(any = false)
          r r' (row, index, i as occ) =
        match
          approx_candidates r r' occ ~map_only:true
        with
        | _, (Zom.Z0 | Zom.Z1 _) ->
          false
        | a, Zom.Zn ->
          if any then
            let f b v = not (branch_on_column r r' b v) in
            not (Array.for_all2_exn a row ~f)
          else
            branch_on_column r r' a.(i) row.(i)

      let branch0 r r' =
        let f0 = branch0_for_occ ~any:false r r'
        and f1 = branch0_for_occ ~any:true r r' in
        let f0 = branch_for_bvar r r' ~f:f0
        and f1 = branch_for_bvar r r' ~f:f1 in
        branch r ~f:f0 || branch r ~f:f1

      (* 
         let branch1 r r' =
         let f v = branch1_for_bvar r r' v in
         let f v = f (Option.value_exn v ~here:_here_) in
         dequeue_exists r_bvar_d ~f
      *)

      let branch_on_diff {r_diff_h} r' (v1, o1) (v2, o2) =
        let doit v1 v2 x =
          let v = Hashtbl.find r_diff_h (v1, v2) in
          let v = Option.value_exn v ~here:_here_ in
          let x = Int63.to_float x in
          bool_of_ok_or_fail (S.ibranch r' v x)
        and d = Int63.(o2 - o1) in
        match v1, v2 with
        | Some v1, Some v2 ->
          if Imt.compare_ivar v1 v2 = 0 then
            false
          else if Imt.compare_ivar v1 v2 > 0 then
            doit v2 v1 d
          else
            doit v1 v2 Int63.(neg d)
        | _, _ ->
          false

      let branch1_for_occ r r' (row, index, i as occ) =
        exists_candidate r r' occ
          ~f:(fun row2 ~bounds ->
            not (Array.for_all2_exn row row2
                   ~f:(fun ov1 ov2 ->
                     not (branch_on_diff r r' ov1 ov2))))

      let branch1 r r' =
        branch r ~f:(branch_for_bvar r r' ~f:(branch1_for_occ r r'))

      let branch2_for_bvar r r' v =
        not (Option.is_some (S.bderef_local r' v)) &&
          bool_of_ok_or_fail (S.bbranch r' v)

      let branch2 r r' =
        branch r ~f:(branch2_for_bvar r r')

      let branch r r' =
        ok_for_true (branch0 r r' || branch1 r r' || branch2 r r')
      
      (* stack management *)

      let push_level _ _ = ()

      let backtrack _ _ = ()

      let backtrack_root _ _ = ()

    end

  end

  module Imt' = Imt.F(Theory_solver)

  module S' = Solver.Make(Imt')(I)

  (* 2nd namespace; to be used for dummy variables *)
  (* module I' = Lang_ids.Make(struct end) *)
  module I' = I

  module C  =  Lang_abstract.Make_term_conv(M)(Lang_abstract.M)

  type ibentry =
    (S'.ovar Lazy.t, S'.xvar Lazy.t) ibeither

  type table_lazy = S'.ovar list list Lazy.t

  type in_constraint_lazy = ibentry list * table_lazy

  type d_boxed = DBox : (I.c, 's) R.t list -> d_boxed

  type ctx = {
    r_ctx           :  S'.ctx;
    r_bg_ctx        :  Imt'.ctx;
    r_theory_ctx    :  Theory_solver.ctx;
    r_table_lazy_h  :  (d_boxed, table_lazy) Hashtbl.t;
    r_in_m          :  (bool_id, in_constraint_lazy list) Hashtbl.t;
  }

  let make_ctx () =
    let r_theory_ctx = Theory_solver.make_ctx () in
    let r_bg_ctx = Imt'.make_ctx r_theory_ctx in {
      r_ctx =
        S'.make_ctx (Imt'.make_ctx r_theory_ctx);
      r_bg_ctx;
      r_theory_ctx;
      (* TODO : monomorphic hashtable *)
      r_table_lazy_h =
        Hashtbl.Poly.create () ~size:32;
      r_in_m = 
        Hashtbl.create () ~size:10240 ~hashable:hashable_bool_id;
    }

  let rec get_dummy_row :
  type s . s S.t -> (I'.c, s) R.t =
    function
    | S.S_Int ->
      R.R_Int (M.M_Var (I'.gen_id Lang_types.Y_Int))
    | S.S_Bool ->
      R.R_Bool (M.M_Var (I'.gen_id Lang_types.Y_Bool))
    | S.S_Pair (a, b) ->
      R.R_Pair (get_dummy_row a, get_dummy_row b)

  let rec get_dummy_row_db :
  type s . (I'.c, s) D.t -> (I'.c, s) R.t =
    function
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
      R.R_Int (M.M_Var (I.gen_id Lang_types.Y_Int))
    | S.S_Bool ->
      R.R_Bool (M.M_Var (I.gen_id Lang_types.Y_Bool))
    | S.S_Pair (a, b) ->
      R.R_Pair (get_symbolic_row a, get_symbolic_row b)

  let rec get_symbolic_row_db :
  type s . (I.c, s) D.t -> (I.c, s) R.t =
    function
    | D.D_Input (s, _) ->
      get_symbolic_row s
    | D.D_Cross (a, b) ->
      R.R_Pair (get_symbolic_row_db a, get_symbolic_row_db b)
    | D.D_Sel (a, _) ->
      get_symbolic_row_db a
  
  let rec has_db_atom = function
    | Formula.F_True ->
      false
    | Formula.F_Atom (A.A_Exists _) ->
      true
    | Formula.F_Atom _ ->
      false
    | Formula.F_Not g ->
      has_db_atom g
    | Formula.F_And (g, h) ->
      has_db_atom g || has_db_atom h
    | Formula.F_Ite (q, g, h) ->
      has_db_atom q || has_db_atom g || has_db_atom h

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

  let rec existential b = function
    | Formula.F_True ->
      true
    | Formula.F_Atom (A.A_Exists d) ->
      b && existential_inside_db d
    | Formula.F_Atom _ ->
      true
    | Formula.F_Not g ->
      existential (not b) g
    | Formula.F_And (g, h) ->
      existential b g && existential b h
    | Formula.F_Ite (q, g, h) ->
      not (has_db_atom q) && existential b g && existential b h

  and existential_inside_db :
  type s . (I.c, s) D.t -> bool =
    function
    | D.D_Input _ ->
      true
    | D.D_Cross (a, b) ->
      existential_inside_db a && existential_inside_db b
    | D.D_Sel (a, f) ->
      existential_inside_db a &&
        existential true (f (get_dummy_row_db a))

  let register_membership_bulk {r_in_m} b l =
    Hashtbl.change r_in_m b
      (function
      | Some l1 -> Some (List.append l l1)
      | None -> Some l)

  let fv = {Lang_ids.f_id = Fn.id}

  let rec list_of_row_aux :
  type s. ibentry list -> ctx -> (I.c, s) R.t ->
    ibentry list =
    fun acc ({r_ctx} as x) r ->
      match r with
      | R.R_Int m ->
        let m = C.map_non_atomic m ~f:(purify_atom x) ~fv in
        let m = S'.ovar_of_term r_ctx m in
        H_Int m :: acc
      | R.R_Bool m ->
        let m = C.map_non_atomic m ~f:(purify_atom x) ~fv in
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
      Hashtbl.find_or_add r_table_lazy_h (DBox l)
        ~default:(fun () ->
          (* maybe we can get rid of the intermediate list *)
          let ll = List.map l ~f:(list_of_row x) in
          lazy (List.map ll ~f:(force_row x)))

  and purify_membership :
  type s . ?acc:(in_constraint_lazy list) -> ctx ->
    (I.c, s) D.t -> (I.c, s) R.t ->
    in_constraint_lazy list * I.c Lang_abstract.A.t Formula.t =
    fun ?acc:(acc = []) x d r ->
      match d, r with
      | D.D_Input (_, l), _ ->
        let ll = table_lazy_of_db x l
        and rl = list_of_row x r in
        (rl, ll) :: acc, Formula.true'
      | D.D_Cross (d1, d2), R.R_Pair (r1, r2) ->
        let acc, g1 = purify_membership ~acc x d1 r1 in
        let acc, g2 = purify_membership ~acc x d2 r2 in
        acc, Formula.(g1 && g2)
      | D.D_Sel (d, f), _ ->
        let g1 = purify_formula x (f r) in
        let acc, g2 = purify_membership ~acc x d r in
        acc, Formula.(g1 && g2)

  and purify_atom :
  ctx -> I.c A.t -> I.c Lang_abstract.A.t Formula.t =
  fun ({r_ctx} as x) -> function
    | A.A_Exists d ->
      let l, g =
        let r = get_symbolic_row_db d in
        purify_membership x d r
      and b = I.gen_id Lang_types.Y_Bool in
      register_membership_bulk x b l;
      Formula.(&&)
        (Formula.F_Atom
           (Lang_abstract.A.A_Bool
              (Lang_abstract.M.M_Var b))) g
    | A.A_Bool b ->
      Formula.F_Atom
        (Lang_abstract.A.A_Bool
           (C.map_non_atomic b ~f:(purify_atom x) ~fv))
    | A.A_Le s ->
      Formula.F_Atom
        (Lang_abstract.A.A_Le
           (C.map_non_atomic s ~f:(purify_atom x) ~fv))
    | A.A_Eq s ->
      Formula.F_Atom
        (Lang_abstract.A.A_Eq
           (C.map_non_atomic s ~f:(purify_atom x) ~fv))

  and purify_formula x =
    Formula.map_non_atomic ~f:(purify_atom x)

  let purify_formula_top x g =
    if existential true g then
      Some (purify_formula x g)
    else
      None

  let assert_formula ({r_ctx} as x) g =
    match purify_formula_top x g with
    | Some g ->
      S'.assert_formula r_ctx g;
      `Ok
    | None ->
      `Fail

  let name_diff r v1 v2 =
    let v = Imt'.new_ivar r (T_Int (None, None)) in
    Int63.(Imt'.add_eq r [minus_one, v1; one, v2; one, v] zero);
    v

  let solve ({r_ctx; r_bg_ctx; r_theory_ctx; r_in_m} as x) =
    Hashtbl.iter r_in_m
      ~f:(fun ~key ~data ->
        let v = S'.bvar_of_id r_ctx key
        and fd = name_diff r_bg_ctx in
        List.iter data
          ~f:(fun (e, l) ->
            Theory_solver.assert_membership
              r_theory_ctx
              v (force_row x e) (Lazy.force l) ~fd));
    S'.solve r_ctx

  let deref_int {r_ctx} i =
    S'.deref_int r_ctx i

  let deref_bool {r_ctx} i =
    S'.deref_bool r_ctx i

end
