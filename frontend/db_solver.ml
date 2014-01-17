open Core.Std
open Db_logic
open Terminology
open Core.Int_replace_polymorphic_compare
open Bounds

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

let dequeue_fold_responses d ~f =
  Dequeue.fold d ~init:N_Ok
    ~f:(fun acc x ->
      match acc with
      | N_Unsat ->
        N_Unsat
      | _ ->
        match f x with
        | N_Ok ->
          acc
        | r ->
          r)

let dequeue_exists_with_swap d ~f =
  let rec g i n = 
    if i <= n then
      let a = Dequeue.get d i in
      let a = Option.value_exn a ~here:_here_ in
      if f a then
        true
      else
        (Dequeue.drop_front d;
         Dequeue.enqueue_back d a;
         g (i + 1) n)
    else
      false in
  match Dequeue.front_index d, Dequeue.back_index d with
  | Some i, Some n ->
    g i n
  | _, _ ->
    false

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

module Zom = struct

  type 'a t = Z0 | Z1 of 'a | Zn of int

  let update z x ~equal =
    match z with
    | Z0 ->
      Z1 x
    | Z1 x' when equal x x' ->
      z
    | Z1 _ ->
      Zn 2
    | Zn n ->
      Zn (n + 1)

end

let ok_for_true = function
  | true  -> `Ok
  | false -> `Fail

let bool_of_ok_or_fail = function
  | `Ok   -> true
  | `Fail -> false

let dbg = false

let intercept_bool s b =
  if dbg then Printf.printf "%s: %b\n%!" s b;
  b

let intercept_ok_or_fail s a =
  if dbg then
    (let s2 = match a with `Ok -> "`Ok" | `Fail -> "`Fail" in
     Printf.printf "%s: %s\n%!" s s2);
  a

let intercept_response s r =
  if dbg then
    (let s2 = Sexplib.Conv.string_of_sexp (sexp_of_response r) in
     Printf.printf "%s: %s\n%!" s s2);
  r

module Make (Imt : Imt_intf.S_with_dp) (I : Id.S) = struct

  module Smt = Smtlib_printer.Make(I)

  type int_id = (I.c, int) Id.t
  
  type bool_id = (I.c, bool) Id.t

  let hashable_int_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Id.compare I.compare_c Int.compare;
    sexp_of_t = Id.sexp_of_t I.sexp_of_c Int.sexp_of_t
  }

  let hashable_bool_id = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Id.compare I.compare_c Bool.compare;
    sexp_of_t = Id.sexp_of_t I.sexp_of_c Bool.sexp_of_t
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

  (* We provide a theory solver (module [D]) and instantiate BC(T)
     accordingly ([Imt.F(D)]). *)

  module Theory_solver = struct

    type row = Imt.ivar option offset array
    with compare, sexp_of

    type db = row list
    with compare, sexp_of

    let hashable_db = {
      Hashtbl.Hashable.
      hash = Hashtbl.hash;
      compare = compare_db;
      sexp_of_t = sexp_of_db
    }

    type idiff = Imt.ivar * Imt.ivar
    with compare, sexp_of

    let hashable_idiff = {
      Hashtbl.Hashable.
      hash = Hashtbl.hash;
      compare = compare_idiff;
      sexp_of_t = sexp_of_idiff
    }

    type row_map = row list Int63.Map.t
    with compare, sexp_of

    type index = row_map * row_map * row list
    with compare, sexp_of

    type occ = row * index * int * int option ref
    with compare, sexp_of

    type bounds_array = (Int63.t option * Int63.t option) array
    with compare, sexp_of

    type mbounds_key = bounds_array * row_map
    with compare, sexp_of

    let hashable_mbounds_key = {
      Hashtbl.Hashable.
      hash = Hashtbl.hash;
      compare = compare_mbounds_key;
      sexp_of_t = sexp_of_mbounds_key
    }

    type mbounds_value =
      bounds_array * (row * bounds_array) Zom.t * bool

    type stats = {
      mutable s_propagate     :  int;
      mutable s_check         :  int;
      mutable s_branch        :  int;
      mutable s_push_level    :  int;
      mutable s_backtrack     :  int;
      mutable s_mbounds_fail  :  int;
      mutable s_mbounds_all   :  int;
      mutable s_maxdepth      :  int;
    } with sexp_of

    type ctx = {
      r_idb_h          :  (db, index) Hashtbl.t;
      r_bvar_d         :  Imt.bvar Dequeue.t;
      r_diff_h         :  (idiff, Imt.ivar) Hashtbl.t;
      r_occ_h          :  (Imt.bvar, occ Dequeue.t) Hashtbl.t;
      r_mbounds_h      :  (mbounds_key, mbounds_value) Hashtbl.t;
      r_stats          :  stats;
      mutable r_level  :  int;
    }

    let make_ctx () = {
      r_idb_h =
        Hashtbl.create () ~size:64 ~hashable:hashable_db;
      r_bvar_d =
        Dequeue.create () ~initial_length:31;
      r_diff_h =
        Hashtbl.create () ~size:1024 ~hashable:hashable_idiff;
      r_occ_h =
        Hashtbl.create () ~size:1024 ~hashable:hashable_bvar;
      r_mbounds_h =
        Hashtbl.create () ~size:255 ~hashable:hashable_mbounds_key;
      r_stats = {
        s_propagate = 0;
        s_check = 0;
        s_branch = 0;
        s_push_level = 0;
        s_backtrack = 0;
        s_mbounds_fail = 0;
        s_mbounds_all = 0;
        s_maxdepth = 0;
      };
      r_level = 0;
    }

    let print_stats {r_stats} =
      Sexplib.Sexp.output_hum stdout (sexp_of_stats r_stats);
      print_newline ()

    let all_concrete =
      Array.for_all ~f:(function None, _ -> true | _ -> false)

    let index_of_db_dimension l i =
      List.fold_left l
        ~init:(Int63.Map.empty, Int63.Map.empty, [])
        ~f:(fun (accm1, accm2, accl) data ->
          match Array.get data i with
          | None, key when all_concrete data ->
            Map.add_multi accm1 ~key ~data, accm2, accl
          | None, key ->
            accm1, Map.add_multi accm2 ~key ~data, accl
          | _ ->
            accm1, accm2, data :: accl)

    let index_of_db {r_idb_h} d i =
      let default () = index_of_db_dimension d i in
      Hashtbl.find_or_add r_idb_h d ~default

    let bvar_in_dequeue d v =
      let f x = Imt.compare_bvar x v = 0 in
      Dequeue.exists d ~f

    let rec ivar_of_diff ({r_diff_h} as r) v1 v2 ~fd ~frv =
      if Imt.compare_ivar v1 v2 > 0 then
        ivar_of_diff r v2 v1 ~fd ~frv
      else if Imt.compare_ivar v1 v2 = 0 then
        None
      else
        let default () =
          assert (Imt.compare_ivar v1 v2 < 0);
          fd v1 v2 in
        Some (Hashtbl.find_or_add r_diff_h (v1, v2) ~default)

    let register_diffs r row1 row2 ~fd ~frv =
      Array.iter2_exn row1 row2
        ~f:(fun (v1, _) (v2, _) ->
          match v1, v2 with
          | Some v1, Some v2 when not (Imt.compare_ivar v1 v2 = 0) ->
            let v = ivar_of_diff r v1 v2 ~fd ~frv in
            let v = Option.value_exn v ~here:_here_ in
            frv v
          | Some v, _ | _, Some v ->
            frv v
          | None, None ->
            ())

    let assert_membership
        ({r_bvar_d; r_occ_h} as r) b e l ~fd ~frv =
      let e = Array.of_list e
      and l = List.map l ~f:Array.of_list in
      List.iter l ~f:(register_diffs r e ~fd ~frv);
      let index = index_of_db r l 0 in
      if not (bvar_in_dequeue r_bvar_d b) then
        Dequeue.enqueue_front r_bvar_d b;
      let occ = e, index, 0, ref None in
      let d =
        let initial_length = 64 and never_shrink = false in
        let default = Dequeue.create ~initial_length ~never_shrink in
        Hashtbl.find_or_add r_occ_h b ~default in
      Dequeue.enqueue_front d occ

    module F

      (S : Imt_intf.S_dp_access
       with type ivar = Imt.ivar
       and type bvar = Imt.bvar) =

    struct

      type 'a folded = row -> bounds:bounds_array -> acc:'a -> 'a

      type 'a folded_no_bounds = row -> acc:'a -> 'a

      type 'a mapped = row -> bounds:bounds_array -> 'a

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
        (LL.(lb' <= lb) && LU.(lb <= ub')) ||
          (LU.(lb' <= ub) && UU.(ub <= ub'))

      let bounds_within_for_dim b b' =
        bounds_within_for_dim b b' || bounds_within_for_dim b' b

      let lb_of_diff {r_diff_h} r' v1 v2 =
        if Imt.compare_ivar v1 v2 = 0 then
          Some Int63.zero
        else if Imt.compare_ivar v1 v2 < 0 then
          let open Option in
          Hashtbl.find r_diff_h (v1, v2) >>= S.get_lb_local r'
        else
          let open Option in
          Hashtbl.find r_diff_h (v2, v1) >>=
            S.get_ub_local r' >>| Int63.neg

      let ub_of_diff {r_diff_h} r' v1 v2 =
        if Imt.compare_ivar v1 v2 = 0 then
          Some Int63.zero
        else if Imt.compare_ivar v1 v2 < 0 then
          let open Option in
          Hashtbl.find r_diff_h (v1, v2) >>= S.get_ub_local r'
        else
          let open Option in
          Hashtbl.find r_diff_h (v2, v1) >>=
            S.get_lb_local r' >>| Int63.neg

      let bounds_within a a' =
        Array.for_all2_exn a a' ~f:bounds_within_for_dim

      let equal_row r r' row1 row2 =
        let f ov1 ov2 =
          match ov1, ov2 with
          | (Some v1, o1), (Some v2, o2) ->
            let lb = lb_of_diff r r' v1 v2
            and ub = ub_of_diff r r' v1 v2 in
            (match lb, ub with
            | Some lb, Some ub ->
              Int63.(lb = ub && lb = o2 - o1)
            | _, _ ->
              false)
          | (Some v1, o1), (None, o2) |
              (None, o2), (Some v1, o1) ->
            let lb = S.get_lb_local r' v1
            and ub = S.get_ub_local r' v1 in
            (match lb, ub with
            | Some lb, Some ub ->
              Int63.(lb = ub && lb = o2 - o1)
            | _ ->
              false)
          | (None, o1), (None, o2) ->
            Int63.(o1 = o2) in
        Array.for_all2_exn row1 row2 ~f

      let maybe_equal_rows r r' row a row' a' =
        bounds_within a a' &&
          (Array.for_all2_exn row row'
             ~f:(fun ov1 ov2 ->
               match ov1, ov2 with
               | (Some v1, o1), (Some v2, o2) ->
                 let open Int63 in
                 let d = o2 - o1
                 and lb = lb_of_diff r r' v1 v2
                 and ub = ub_of_diff r r' v1 v2
                 and default = true in
                 Option.value_map lb ~f:((>=) d) ~default &&
                   Option.value_map ub ~f:((<=) d) ~default
               | _ ->
                 true))

      let fold_index
          (m1, m2, l : index)
          ~init ~(f : 'a folded_no_bounds) =
        let f acc data = f data ~acc in
        let f ~key ~data init = List.fold_left data ~init ~f
        and init = List.fold_left l ~f ~init in
        let init = Map.fold m1 ~init ~f in
        Map.fold m2 ~init ~f

      let fold_candidates_list r r' row l i ~init ~(f : 'a folded) =
        let a = bounds_of_row r' row in
        let f acc data =
          let bounds = bounds_of_row r' data  in
          if maybe_equal_rows r r' data bounds row a then
            f data ~bounds ~acc
          else
            acc in
        List.fold_left l ~f ~init

      let fold_constant_candidates
          ({r_stats; r_mbounds_h} as r)
          r' row m i
          ~init ~(f : 'a folded) =
        r_stats.s_mbounds_all <- r_stats.s_mbounds_all + 1;
        let a = bounds_of_row r' row in
        let default () =
          r_stats.s_mbounds_fail <- r_stats.s_mbounds_fail + 1;
          let f acc data =
            let bounds = bounds_of_row r' data  in
            if maybe_equal_rows r r' data bounds row a then
              f data ~bounds ~acc
            else
              acc in
          let f ~key ~data init = List.fold_left data ~init ~f
          and min, max = a.(i) in
          let min = Option.value min ~default:Int63.min_value
          and max = Option.value max ~default:Int63.max_value in
          Map.fold_range_inclusive m ~min ~max ~init ~f
        and key = a, m in
        let r = Hashtbl.find_or_add r_mbounds_h key ~default in
        Tuple3.map1 r ~f:Array.copy

      let fold_candidates_map r r' row m i ~init ~(f : 'a folded) =
        let a = bounds_of_row r' row in
        let f acc data =
          let bounds = bounds_of_row r' data  in
          if maybe_equal_rows r r' data bounds row a then
            f data ~bounds ~acc
          else
            acc in
        let f ~key ~data init = List.fold_left data ~init ~f
        and min, max = a.(i) in
        let min = Option.value min ~default:Int63.min_value
        and max = Option.value max ~default:Int63.max_value in
        Map.fold_range_inclusive m ~min ~max ~init ~f

      let exists_candidate
          r r' (row, (m1, m2, l), i, _) ~(f : bool mapped) =
        let a = bounds_of_row r' row in
        let f data =
          let bounds = bounds_of_row r' data  in
          maybe_equal_rows r r' data bounds row a &&
            f data ~bounds in
        let f ~key ~data acc = acc || List.exists data ~f
        and init = List.exists l ~f in
        init ||
          let min = lb_of_ovar r' row.(i)
          and max = ub_of_ovar r' row.(i) in
          let min = Option.value min ~default:Int63.min_value
          and max = Option.value max ~default:Int63.max_value in
          let init = false in
          Map.fold_range_inclusive m1 ~min ~max ~init ~f ||
            Map.fold_range_inclusive m2 ~min ~max ~init ~f

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

      let foldi_responses_occs {r_occ_h} v ~f =
        match Hashtbl.find r_occ_h v with
        | None ->
          if true then raise (Unreachable.Exn _here_);
          N_Ok
        | Some d ->
          let n = Dequeue.back_index d in
          let n = Option.value_exn n ~here:_here_ in
          let rec g i acc =
            if i <= n then
              match Dequeue.get d i with
              | Some (_, _, _, {contents = _} as o) ->
                (match f i o with
                | N_Unsat ->
                  N_Unsat
                | N_Tightened ->
                  g (i + 1) N_Tightened 
                | N_Ok ->
                  g (i + 1) acc)
              (* | Some _ ->
                g (i + 1) acc *)
              | None ->
                raise (Unreachable.Exn _here_)
            else
              acc in
          let n = Dequeue.front_index d in
          let n = Option.value_exn n ~here:_here_ in
          g n N_Ok

      let for_all_occs {r_occ_h} v ~f =
        match Hashtbl.find r_occ_h v with
        | None ->
          true
        | Some d ->
          Dequeue.for_all d ~f

      let exists_occs {r_occ_h} v ~f =
        match Hashtbl.find r_occ_h v with
        | None ->
          false
        | Some d ->
          dequeue_exists_with_swap d ~f

      let satisfied_occ r r' (row, _, _, _ as occ) =
        let f row' ~bounds = equal_row r r' row row' in
        exists_candidate r r' occ ~f

      (* propagate *)

      type bp = Int63.t option * Int63.t option
      with sexp_of

      let approx_candidates_folded
          ?cnst_only:(cnst_only = false)
          r r' witness_row row ~bounds ~acc:(a, z, s) =
        Array.iteri bounds
          ~f:(fun i (lb, ub) ->
            let lb', ub' = a.(i) in
            if cnst_only then
              match lb, ub with
              | Some lb, Some ub when Int63.compare lb ub = 0 ->
                a.(i) <- (Option.(lb' >>| Int63.min lb),
                          Option.(ub' >>| Int63.max ub))
              | _, _ ->
                ()
            else
              a.(i) <- (Option.map2 lb lb' ~f:Int63.min,
                        Option.map2 ub ub' ~f:Int63.max));
        let equal (_, a) (_, a') =
          let eq1 = Option.equal Int63.equal in
          let equal = Tuple2.equal ~eq1 ~eq2:eq1 in
          Array.equal a a' ~equal
        and s = s || equal_row r r' witness_row row in
        a, Zom.update z (row, bounds) ~equal, s

      let approx_candidates
          ?cnst_only:(cnst_only = false)
          r r' (row, (m1, m2, l), i, _) =
        let n = Array.length row in
        let p = Some Int63.max_value, Some Int63.min_value in
        let init = Array.init ~f:(fun _ -> p) n, Zom.Z0, false
        and f = approx_candidates_folded ~cnst_only r r' row in
        let init = fold_constant_candidates r r' row m1 i ~init ~f in
        let init = fold_candidates_map r r' row m2 i ~init ~f in
        fold_candidates_list r r' row l i ~init ~f

      let fix_variable r v x =
        response_of_attempts
          (S.set_lb_local r v x)
          (S.set_ub_local r v x)

      let assert_ovar_equal {r_diff_h} r' (v1, o1) (v2, o2) =
        let fb b = if b then N_Ok else N_Unsat
        and f v1 v2 x =
          assert (Imt.compare_ivar v1 v2 < 0);
          let v = Hashtbl.find r_diff_h (v1, v2) in
          let v = Option.value_exn v ~here:_here_ in
          fix_variable r' v x
        and d = Int63.(o2 - o1) in
        match v1, v2 with
        | Some v1, Some v2 ->
          if Imt.compare_ivar v1 v2 = 0 then
            fb (Int63.equal o1 o2)
          else if Imt.compare_ivar v1 v2 > 0 then
            f v2 v1 (Int63.neg d)
          else
            f v1 v2 d
        | Some v1, None ->
          fix_variable r' v1 d
        | None, Some v2 ->
          fix_variable r' v2 Int63.(neg d)
        | None, None ->
          fb (Int63.equal o1 o2)

      type db_bounds = (Int63.t option * Int63.t option) list
      with sexp_of

      type occ_state = db_bounds * db_bounds list
      with sexp_of

      let row_state r r' row =
        let f ov = lb_of_ovar r' ov, ub_of_ovar r' ov in
        List.map (Array.to_list row) ~f

      let index_state r r' (ix : index) =
        let init = [] and f row ~acc = row_state r r' row :: acc in
        fold_index ix ~init ~f

      let occ_state r r' (row, index, i, {contents = i'} : occ) =
        row_state r r' row, index_state r r' index

      let propagate_for_occ ({r_level} as r) r' = function
        | _, _, _, {contents = Some _} ->
          N_Ok
        | row, _, i, s as occ ->
          match approx_candidates r r' occ with
          | _, Zom.Z0, _ ->
            (* no candidates *)
            N_Unsat
          | _, Zom.Z1 (row2, _), b ->
            (* propagate bounds *)
            if b then s := Some r_level;
            let f i = assert_ovar_equal r r' row.(i) in
            array_foldi_responses row2 ~f
          | a, Zom.Zn _, b ->
            if b then s := Some r_level;
            array_foldi_responses a
              ~f:(fun i (lb, ub) ->
                let rl = maybe_lower_bound_ovar r r' lb row.(i)
                and ru = maybe_upper_bound_ovar r r' ub row.(i) in
                response_of_attempts rl ru)

      let propagate_for_occ r r' occ =
        intercept_response "propagate_for_occ"
          (propagate_for_occ r r' occ)

      let propagate_for_bvar_aux r r' v =
        intercept_response "propagate_for_bvar_aux"
          (let f _ = propagate_for_occ r r' in
           foldi_responses_occs r v ~f)

      let propagate_for_bvar r r' v =
        intercept_response "propagate_for_bvar"
          (Option.value_map (S.bderef_local r' v)
             ~f:(function true ->
               propagate_for_bvar_aux r r' v
             | false ->
               N_Ok)
             ~default:N_Ok)

      let propagate ({r_stats; r_bvar_d} as r) r' =
        r_stats.s_propagate <- r_stats.s_propagate + 1;
        let f = propagate_for_bvar r r' in
        intercept_response "propagate"
          (dequeue_fold_responses r_bvar_d ~f)

      (* check given solution *)
            
      let deref_ovar_sol r' sol = function
        | Some v, o ->
          Int63.(S.ideref_sol r' sol v + o)
        | None, o ->
          o

      let matches_row r' sol row_concrete row =
        Array.for_all2_exn row row_concrete
          ~f:(fun ov c -> Int63.equal (deref_ovar_sol r' sol ov) c)

      let exists_index (m1, m2, l) ~f ~min ~max =
        List.exists l ~f ||
          let f ~key ~data acc = acc || List.exists data ~f in
          Map.fold_range_inclusive m1 ~min ~max ~init:false ~f ||
            Map.fold_range_inclusive m2 ~min ~max ~init:false ~f 

      let check_for_occ r r' sol ((row, index, i, _) : occ) =
        let row = Array.map row ~f:(deref_ovar_sol r' sol) in
        let f = matches_row r' sol row in
        exists_index index ~min:row.(i) ~max:row.(i) ~f

      let check_for_bvar ({r_occ_h} as r) r' sol v =
        not (S.bderef_sol r' sol v) ||
          for_all_occs r v ~f:(check_for_occ r r' sol)

      let check ({r_stats; r_bvar_d} as r) r' sol =
        r_stats.s_check <- r_stats.s_check + 1;
        let f = check_for_bvar r r' sol in
        intercept_bool "check" (Dequeue.for_all r_bvar_d ~f)

      (* branching *)

      let branch_for_bvar r r' v ~f =
        match S.bderef_local r' v with
        | Some true ->
          exists_occs r v ~f
        | _ ->
          false

      let branch {r_bvar_d} ~f =
        dequeue_exists_with_swap r_bvar_d ~f

      let branch_on_column r r' (lb, ub) ov n =
        let lb =
          let lb' = lb_of_ovar r' ov in
          if LL.(lb <= lb') then lb' else lb
        and ub =
          let ub' = ub_of_ovar r' ov in
          if UU.(ub' <= ub) then ub' else ub in
        let lb = Option.value_exn lb ~here:_here_
        and ub = Option.value_exn ub ~here:_here_ in
        not (Int63.(equal lb max_value)) &&
          not (Int63.(equal ub min_value)) &&
          not (Int63.equal lb ub) &&
          match ov with
          | Some v, o ->
            let middle = Int63.((lb + ub) / (one + one) - o) in
            let middle = Int63.to_float middle
            and range = Int63.to_float ub -. Int63.to_float lb in
            bool_of_ok_or_fail
              (S.ibranch r' v 
                 (if n <= 50 && Float.(range <= of_int 50) then
                     (ignore (range);
                      middle +. 0.5)
                  else
                     middle))
          | None, _ ->
            false

      let branch0_for_occ ?any:(any = false)
          r r' (row, _, i, _ as occ) =
        match
          approx_candidates r r' occ ~cnst_only:true
        with
        | _, (Zom.Z0 | Zom.Z1 _), _ ->
          false
        | a, Zom.Zn n, _ ->
          if any then
            let f b v = not (branch_on_column r r' b v n) in
            not (Array.for_all2_exn a row ~f)
          else
            branch_on_column r r' a.(i) row.(i) n

      let branch0_for_occ ?any:(any = false) r r' (_, _, _, s as occ) =
        match s with
        | {contents = Some _} ->
          false
        | _ ->
          branch0_for_occ ~any r r' occ

      let branch0 r r' =
        let f = branch0_for_occ ~any:false r r' in
        let f = branch_for_bvar r r' ~f in
        branch r ~f

      let branch0_5 r r' =
        let f = branch0_for_occ ~any:true r r' in
        let f = branch_for_bvar r r' ~f in
        branch r ~f

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
            doit v2 v1 (Int63.neg d)
          else
            doit v1 v2 d
        | _, _ ->
          false

      let branch1_for_occ r r' (row, index, i, _ as occ) =
        let f row2 ~bounds =
          let f ov1 ov2 = not (branch_on_diff r r' ov1 ov2) in
          not (Array.for_all2_exn row row2 ~f) in
        exists_candidate r r' occ ~f

      let branch1_for_occ r r' (_, _, _, s as occ) =
        match s with
        | {contents = Some _} ->
          false
        | _ ->
          branch1_for_occ r r' occ

      let branch1 r r' =
        branch r ~f:(branch_for_bvar r r' ~f:(branch1_for_occ r r'))

      let branch2_for_bvar r r' v =
        not (Option.is_some (S.bderef_local r' v)) &&
          bool_of_ok_or_fail (S.bbranch r' v)

      let branch2 r r' =
        branch r ~f:(branch2_for_bvar r r')

      let branch ({r_stats} as r) r' =
        try
          r_stats.s_branch <- r_stats.s_branch + 1;
          ok_for_true
            (branch0 r r' ||
               branch0_5 r r' ||
               branch1 r r' ||
               branch2 r r')
        with
        | e ->
          (Printf.printf "exception: %s\n%!p" (Exn.to_string e);
           raise e)
      
      (* stack management *)

      let push_level ({r_stats} as r) _ =
        r.r_level <- r.r_level + 1;
        r_stats.s_maxdepth <- max r_stats.s_maxdepth r.r_level;
        r_stats.s_push_level <- r_stats.s_push_level + 1

      let backtrack ({r_occ_h; r_stats} as r) _ =
        assert (r.r_level >= 0);
        r.r_level <- r.r_level - 1;
        (let f ~key ~data =
           let f = function
             | (_, _, _, ({contents = Some c} as rf))
                 when c >= r.r_level ->
               rf := None
             | _ ->
               () in
           Dequeue.iter data ~f in
         Hashtbl.iter r_occ_h ~f);
        r_stats.s_backtrack <- r_stats.s_backtrack + 1

    end

  end

  module Imt' = Imt.F(Theory_solver)

  module S' = Solver.Make(Imt')(I)

 module C =  Logic.Make_term_conv(M)(Logic.M)

  type ibentry =
    (S'.ovar Lazy.t, S'.xvar Lazy.t) ibeither

  type table_lazy = S'.ovar list list Lazy.t

  type in_constraint_lazy = ibentry list * table_lazy

  type d_boxed = DBox : (I.c, 's) R.t list -> d_boxed

  type mode = [`Eager | `Smt_out | `Lazy]
  
  type ctx = {
    r_ctx           :  S'.ctx;
    r_bg_ctx        :  Imt'.ctx;
    r_theory_ctx    :  Theory_solver.ctx;
    r_mode          :  mode;
    r_table_lazy_h  :  (d_boxed, table_lazy) Hashtbl.t;
    r_in_m          :  (bool_id, in_constraint_lazy list) Hashtbl.t;
    r_smtlib_ctx    :  Smt.ctx option;
  }

  let make_ctx r_mode =
    let r_theory_ctx = Theory_solver.make_ctx () in
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
    | D.D_Rel (_, f) ->
      (* FIXME: looks fine, but think about it again *)
      not under_forall
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

  let assert_formula ({r_ctx} as x) g =
    match purify_formula_top x g with
    | Some g ->
      S'.assert_formula r_ctx g; `Ok
    | None ->
      `Out_of_fragment

  let name_diff r v1 v2 =
    let v = Imt'.new_ivar r (T_Int (None, None)) in
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
          Theory_solver.assert_membership
            r_theory_ctx
            v (force_row x e) (Lazy.force l) ~fd ~frv in
        List.iter data ~f in
      Hashtbl.iter r_in_m ~f;
      let r = S'.solve r_ctx in
      Theory_solver.print_stats r_theory_ctx; r
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
