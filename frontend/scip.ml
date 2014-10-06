open Core.Std
open Scip_idl
open Terminology
open Core.Int_replace_polymorphic_compare

exception Scip_Exn of (Here.t * retcode)

(* implementation first, then wrapping things up in modules and
   functors *)

type scip_ctx = {
  r_ctx: scip;
  r_var_d: var Dequeue.t;
  mutable r_cch: cch option;
  mutable r_constraints_n: int;
  mutable r_has_objective: bool;
  mutable r_sol: sol option;
  mutable r_cuts_n: int;
}

let dummy_f = ""

let dummy_var = cc_handler_zero_var ()

type var = Scip_idl.var

let compare_var x y =
  Int.compare (uintptr_t_of_var x) (uintptr_t_of_var y)

let hash_var = uintptr_t_of_var

let sexp_of_var v =
  Sexplib.Conv.sexp_of_string
    (if compare_var v dummy_var = 0 then
        "NULL"
     else
        sCIPvarGetName v)

let ivar_of_bvar x = x

(* TODO : check bounds *)
let bvar_of_ivar x = x

type named_constraint = cons

let string_of_retcode = function
  |  SCIP_OKAY  ->
    "SCIP_OKAY"
  |  SCIP_ERROR  ->
    "SCIP_ERROR"
  |  SCIP_NOMEMORY  ->
    "SCIP_NOMEMORY"
  |  SCIP_READERROR  ->
    "SCIP_READERROR"
  |  SCIP_WRITEERROR  ->
    "SCIP_WRITEERROR"
  |  SCIP_NOFILE  ->
    "SCIP_NOFILE"
  |  SCIP_FILECREATEERROR  ->
    "SCIP_FILECREATEERROR"
  |  SCIP_LPERROR  ->
    "SCIP_LPERROR"
  |  SCIP_NOPROBLEM  ->
    "SCIP_NOPROBLEM"
  |  SCIP_INVALIDCALL  ->
    "SCIP_INVALIDCALL"
  |  SCIP_INVALIDDATA  ->
    "SCIP_INVALIDDATA"
  |  SCIP_INVALIDRESULT  ->
    "SCIP_INVALIDRESULT"
  |  SCIP_PLUGINNOTFOUND  ->
    "SCIP_PLUGINNOTFOUND"
  |  SCIP_PARAMETERUNKNOWN  ->
    "SCIP_PARAMETERUNKNOWN"
  |  SCIP_PARAMETERWRONGTYPE  ->
    "SCIP_PARAMETERWRONGTYPE"
  |  SCIP_PARAMETERWRONGVAL  ->
    "SCIP_PARAMETERWRONGVAL"
  |  SCIP_KEYALREADYEXISTING  ->
    "SCIP_KEYALREADYEXISTING"
  |  SCIP_MAXDEPTHLEVEL  ->
    "SCIP_MAXDEPTHLEVEL"

let ok_or_fail_of_retcode = function
  | SCIP_OKAY ->
    `Ok
  | _ ->
    `Fail

let assert_ok loc = function
  | SCIP_OKAY ->
    ()
  | v ->
    raise (Scip_Exn (loc, v))

let assert_ok1 loc = function
  | SCIP_OKAY, r ->
    r
  | v, _ ->
    raise (Scip_Exn (loc, v))

let assert_ok2 loc = function
  | SCIP_OKAY, r1, r2 ->
    r1, r2
  | v, r1, r2 ->
    raise (Scip_Exn (loc, v))

let string_of_version () =
  Printf.sprintf "%d.%d.%d"
    (sCIPmajorVersion ())
    (sCIPminorVersion ())
    (sCIPtechVersion ())

let config_list = [
  (* _here_, *)
  (* (fun c -> sCIPsetEmphasis c SCIP_PARAMEMPHASIS_FEASIBILITY true); *)
  _here_,
  (fun c -> sCIPsetIntParam c "display/verblevel" 0);
  _here_,
  (fun c -> sCIPsetHeuristics c SCIP_PARAMSETTING_AGGRESSIVE true);
  _here_,
  (fun c -> sCIPsetSeparating c SCIP_PARAMSETTING_AGGRESSIVE true);
  _here_,
  (fun c -> sCIPsetPresolving c SCIP_PARAMSETTING_OFF true);
  (* _here_, *)
  (* (fun c -> sCIPsetBoolParam c "presolving/donotmultaggr" true); *)
  (* _here_, *)
  (* (fun c -> sCIPsetBoolParam c "presolving/donotaggr" true); *)
]

let run_config_list c =
  List.iter config_list ~f:(fun (h, f) -> assert_ok h (f c))

let make_ctx () =
  let r_ctx = assert_ok1 _here_ (sCIPcreate ()) in
  let r_cch = Some (new_cc_handler r_ctx None None) in
  cc_handler_include (Option.value_exn r_cch ~here:_here_);
  assert_ok _here_ (sCIPincludeDefaultPlugins_modified r_ctx);
  assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
  run_config_list r_ctx;
  let r_var_d = Dequeue.create () ~initial_length:1023
  and r_constraints_n = 0
  and r_has_objective = false
  and r_sol = None 
  and r_cuts_n = 0 in
  {r_ctx; r_cch; r_var_d; r_constraints_n; r_has_objective;
   r_sol; r_cuts_n}

let new_f _ id _ = id

let scip_lb {r_ctx} =
  Option.value_map
    ~default:(~-. (sCIPinfinity r_ctx))
    ~f:Int63.to_float

let scip_ub {r_ctx} =
  Option.value_map
    ~default:(sCIPinfinity r_ctx)
    ~f:Int63.to_float

let scip_lb_float {r_ctx} =
  Option.value ~default:(~-. (sCIPinfinity r_ctx))

let scip_ub_float {r_ctx} =
  Option.value ~default:(sCIPinfinity r_ctx)

let new_ivar ({r_ctx; r_var_d} as r) t =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (match t with
      | T_Int (lb, ub) ->
        sCIPcreateVarBasic
          r_ctx id (scip_lb r lb) (scip_ub r ub)
          0. SCIP_VARTYPE_INTEGER
      | T_Real (lb, ub) ->
        sCIPcreateVarBasic
          r_ctx id (scip_lb_float r lb) (scip_ub_float r ub)
          0. SCIP_VARTYPE_CONTINUOUS) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.enqueue_back r_var_d v; v

let new_bvar {r_ctx; r_var_d} =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (sCIPcreateVarBasic r_ctx id 0.0 1.0 0. SCIP_VARTYPE_BINARY) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.enqueue_back r_var_d v; v

let negate_bvar {r_ctx; r_var_d} v =
  let v = assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v) in
  Dequeue.enqueue_back r_var_d v; v

let iexpr_vars (l, o) =
  Array.of_list (List.map l ~f:snd)

let make_constraint_id ({r_constraints_n} as r) =
  let id = Printf.sprintf "c%d" r_constraints_n in
  r.r_constraints_n <- r_constraints_n + 1;
  id

let create_constraint ({r_ctx} as r) eq l o =
  assert_ok1 _here_
    (sCIPcreateConsBasicLinear r_ctx
       (make_constraint_id r)
       (Array.of_list_map ~f:snd l)
       (let f (x, _) = Int63.to_float x in
        Array.of_list_map ~f l)
       (-.
           (if eq then
               Int63.(to_float (neg o))
            else
               sCIPinfinity r_ctx))
       (Int63.to_float o))

let add_eq ({r_ctx} as r) l o =
  let c = create_constraint r true l o in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_le ({r_ctx} as r) l o =
  let c = create_constraint r false l o in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let var_of_var_signed {r_ctx} = function
  | S_Pos v ->
    v
  | S_Neg v ->
    assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v)

let add_indicator ({r_ctx} as r) v l o =
  let c =
    assert_ok1 _here_
      (sCIPcreateConsBasicIndicator r_ctx
         (make_constraint_id r)
         (var_of_var_signed r v)
         (Array.of_list_map ~f:snd l)
         (let f (x, _) = Int63.to_float x in
          Array.of_list_map ~f l)
         (Int63.to_float o)) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_clause ({r_ctx; r_constraints_n} as r) l =
  let c =
    assert_ok1 _here_
      (let l =
         Array.of_list_map l
           ~f:(function
           | S_Pos v ->
             v
           | S_Neg v ->
             assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v)) in
       sCIPcreateConsBasicLogicor r_ctx (make_constraint_id r) l) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let var_of_var_option {r_cch} =
  Option.value ~default:dummy_var

let add_call ({r_cch} as r) (v, o) f l =
  Scip_idl.cc_handler_call (Option.value_exn r_cch ~here:_here_)
    (var_of_var_option r v) (Int63.to_int64 o) f
    (let f (x, _) = var_of_var_option r x in
     Array.of_list_map l ~f)
    (let f (_, x) = Int63.to_int64 x in
     Array.of_list_map l ~f)

let add_objective {r_ctx; r_has_objective} l =
  if r_has_objective then
    `Duplicate
  else
    (List.iter l
       ~f:(fun (c, v) ->
         let c = Int63.to_float c in
         assert_ok _here_ (sCIPchgVarObj r_ctx v c));
     `Ok)

let result_of_status = function
  | SCIP_STATUS_OPTIMAL ->
    R_Opt
  | SCIP_STATUS_UNBOUNDED ->
    R_Unbounded
  | SCIP_STATUS_INFEASIBLE ->
    R_Unsat
  | _ ->
    R_Unknown

let sresult_of_response = function
  | N_Ok -> SCIP_DIDNOTFIND
  | N_Unsat -> SCIP_CUTOFF
  | N_Tightened -> SCIP_REDUCEDDOM

let write_ctx {r_ctx} filename =
  assert_ok _here_ (sCIPwriteOrigProblem r_ctx filename "lp" false)

let solve ({r_ctx; r_cch} as r) =
  cc_handler_finalize (Option.value_exn r_cch ~here:_here_);
  assert_ok _here_ (sCIPsolve r_ctx);
  let rval = result_of_status (sCIPgetStatus r_ctx) in
  (match rval with
  | R_Opt | R_Unbounded | R_Sat ->
    r.r_sol <- Some (sCIPgetBestSol r_ctx)
  | _ -> ());
  rval

let ideref_sol {r_ctx} sol v =
  let x = sCIPgetSolVal r_ctx sol v in
  let i = Int63.of_float x in
  if Float.(x > Int63.to_float i + 0.5) then
    Int63.succ i
  else
    i

let bderef_sol {r_ctx} sol v =
  Float.(>) (sCIPgetSolVal r_ctx sol v) 0.5

let ideref ({r_sol} as r) v =
  Option.map r_sol ~f:(fun s -> ideref_sol r s v)

let bderef ({r_sol} as r) v =
  Option.map r_sol ~f:(fun s -> bderef_sol r s v)

let branch {r_ctx} v x =
  let lb = sCIPvarGetLbLocal v
  and ub = sCIPvarGetUbLocal v in
  if Float.(lb < ub && lb <= x && ub >= x) then
    let r, _, _, _ = sCIPbranchVarVal r_ctx v x in
    ok_or_fail_of_retcode r
  else
    `Fail

let variables_number {r_var_d} = Dequeue.length r_var_d

let constraints_number {r_constraints_n} = r_constraints_n

let make_cut_id ({r_cuts_n} as r) =
  let id = Printf.sprintf "c%d" r_cuts_n in
  r.r_cuts_n <- r_cuts_n + 1;
  id

let add_cut_local ({r_ctx} as r) (l, o) =
  let row =
    assert_ok1 _here_
      (sCIPcreateEmptyRowCons r_ctx
         (sCIPfindConshdlr r_ctx "cc")
         (make_cut_id r)
         (-. (sCIPinfinity r_ctx)) Int63.(to_float (- o))
         true false false) in
  let vars = Array.of_list_map ~f:snd l
  and coefs =
    let f (x, _) = Int63.to_float x in
    Array.of_list_map ~f l in
  assert_ok _here_ (sCIPaddVarsToRow r_ctx row vars coefs);
  if
    assert_ok1 _here_ (sCIPaddCut r_ctx (scip_null_sol ()) row true)
  then
    `Unsat
  else
    `Ok

(* FIXME : do we really need the Option? *)
let name_diff {r_cch} v1 v2 o =
  let r_cch = Option.value_exn r_cch ~here:_here_ in
  Some (cc_handler_add_dvar r_cch v1 v2 (Int63.to_int64 o) true)

let add_diffs_disjunction ({r_ctx; r_cch} as r) l =
  let r_cch = Option.value_exn r_cch ~here:_here_ in
  let name_diff v1 v2 o =
    cc_handler_add_dvar r_cch v1 v2 (Int63.to_int64 o) false in
  let (>>|) = Option.(>>|) in
  let l =
    let f acc = function
      | ((Some v1, o1), (Some v2, o2)) when
          compare_var v1 v2 > 0 ->
        acc >>| (fun l ->
          let d =
            let o = Int63.(o2 - o1) in
            name_diff v1 v2 o, o, SCIP_BOUNDTYPE_UPPER in
          d :: l)
      | ((Some v1, o1), (Some v2, o2)) when
          compare_var v1 v2 < 0 ->
        acc >>| (fun l ->
          let d =
            let o = Int63.(o1 - o2) in
            name_diff v2 v1 o, o, SCIP_BOUNDTYPE_LOWER in
          d :: l)
      | (Some _, o1), (Some _, o2)
      | (None, o1), (None, o2) ->
        if Int63.(o1 <= o2) then
          None
        else
          acc
      | (Some v1, o1), (None, o2) ->
        acc >>| (fun l ->
          let o = Int63.(o2 - o1) in
          (v1, o, SCIP_BOUNDTYPE_UPPER) :: l)
      | (None, o1), (Some v2, o2) ->
        acc >>| (fun l ->
          let o = Int63.(o1 - o2) in
          (v2, o, SCIP_BOUNDTYPE_LOWER) :: l)
    and init = Some [] in
    List.fold_left l ~f ~init in
  match l with
  | Some l ->
    let vars = Array.of_list_map ~f:Tuple.T3.get1 l
    and bounds =
      let f (_, x, _) = Int63.to_float x in
      Array.of_list_map ~f l
    and types = Array.of_list_map ~f:Tuple.T3.get3 l in
    let c =
      assert_ok1 _here_
        (sCIPcreateConsBasicBounddisjunction r_ctx 
           (make_constraint_id r)
           vars types bounds) in
    assert_ok _here_ (sCIPaddCons r_ctx c)
  | None ->
    ()

module Types = struct
  type ctx = scip_ctx
  type ivar = var
  type bvar = var
  let compare_ivar = compare_var
  let hash_ivar = hash_var
  let sexp_of_ivar = sexp_of_var
  let compare_bvar = compare_var
  let hash_bvar = hash_var
  let sexp_of_bvar = sexp_of_var
  let ivar_of_bvar = ivar_of_bvar
  let bvar_of_ivar = bvar_of_ivar
end

module Types_uf = struct
  type f = string
  let compare_f = String.compare
  let hash_f = String.hash
  let sexp_of_f = String.sexp_of_t
  let dummy_f = dummy_f
end

module Access = struct
  let new_f = new_f
  let new_ivar = new_ivar
  let new_bvar = new_bvar
  let negate_bvar = negate_bvar
  let add_eq = add_eq
  let add_le = add_le
  let add_indicator = add_indicator
  let add_clause = add_clause
  let add_call = add_call
  let add_objective = add_objective
  let add_diffs_disjunction = add_diffs_disjunction
  let solve = solve
  let ideref = ideref
  let bderef = bderef
  let write_ctx = write_ctx
  let name_diff = name_diff
end

module Dp_access_bounds = struct

  include Types

  type sol' = sol

  type sol = sol'

  let get_lb_local {r_ctx} v =
    let lb = sCIPvarGetLbLocal v in
    if sCIPisEQ r_ctx lb (-. (sCIPinfinity r_ctx)) then
      None
    else
      Some (Int63.of_float lb)

  let get_ub_local {r_ctx} v =
    let ub = sCIPvarGetUbLocal v in
    if sCIPisEQ r_ctx ub (sCIPinfinity r_ctx) then
      None
    else
      Some (Int63.of_float ub)

  let bderef_local r v =
    Option.(get_lb_local r v >>| Int63.((<=) one))

  let set_lb_local {r_ctx} v x =
    let infeasible, tightened =
      let cons = scip_null_cons ()
      and x = Int63.to_float x in
      assert_ok2 _here_ (sCIPinferVarLbCons r_ctx v x cons 0 true) in
    if infeasible then
      `Infeasible
    else if tightened then
      `Tightened
    else
      `Ok

  let set_ub_local {r_ctx} v x =
    let infeasible, tightened =
      let cons = scip_null_cons ()
      and x = Int63.to_float x in
      assert_ok2 _here_ (sCIPinferVarUbCons r_ctx v x cons 0 true) in
    if infeasible then
      `Infeasible
    else if tightened then
      `Tightened
    else
      `Ok

  let ideref_sol = ideref_sol

  let bderef_sol = bderef_sol

end

module Dp_access = struct

  include Dp_access_bounds

  let ibranch = branch

  let ibranch_nary {r_ctx} v ~middle ~n ~width =
    let r, n = sCIPbranchVarValNary r_ctx v middle n width 1. in
    match r with
    | SCIP_OKAY ->
      if n > 0 then
        `Ok
      else
        raise (Scip_Exn (_here_, SCIP_OKAY))
    | _ ->
      `Fail

  let bbranch r v = branch r v 0.5

end

module Cut_gen_access = struct

  include Dp_access_bounds

  let add_cut_local = add_cut_local

end

module Scip_basic : Imt_intf.S_unit_creatable = struct
  include Types
  include Types_uf
  include Access
  let make_ctx = make_ctx
end

module Scip_with_dp = struct

  include Types
  include Types_uf

  module F

    (D : Imt_intf.S_dp
     with type ivar_plug := ivar
     and type bvar_plug := bvar) =

  struct

    module D' = D.F(Dp_access)

    include Types
    include Types_uf
    include Access

    let make_dp d_ctx ctx =
      make_dP (object
        method push_level =
          D'.push_level d_ctx ctx
        method backtrack =
          D'.backtrack d_ctx ctx
        method propagate =
          sresult_of_response (D'.propagate d_ctx ctx)
        method check =
          D'.check d_ctx ctx
        method branch =
          match D'.branch d_ctx ctx with
          | `Ok ->
            true
          | `Fail ->
            false
      end)

    let make_ctx d =
      let r_ctx = assert_ok1 _here_ (sCIPcreate ())
      and r_cch = None
      and r_var_d = Dequeue.create ()
      and r_constraints_n = 0
      and r_has_objective = false
      and r_sol = None
      and r_cuts_n = 0 in
      let rval = {
        r_ctx;
        r_cch;
        r_var_d;
        r_constraints_n;
        r_has_objective;
        r_sol;
        r_cuts_n
      } in
      let o = Some (make_dp d rval) in
      let r_cch = Some (new_cc_handler r_ctx o None) in
      rval.r_cch <- r_cch;
      cc_handler_include (Option.value_exn rval.r_cch ~here:_here_);
      assert_ok _here_ (sCIPincludeDefaultPlugins_modified r_ctx);
      assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
      run_config_list r_ctx;
      rval
    
    let register_var {r_cch} v =
      let r_cch = Option.value_exn ~here:_here_ r_cch in
      cc_handler_catch_var_events r_cch v

    let register_ivar = register_var

    let register_bvar = register_var

  end

end

module Scip_with_cut_gen = struct

  include Types
  include Types_uf
    
  type sol' = sol
    
  type sol = sol'

  module F

    (D : Imt_intf.S_cut_gen
     with type ivar_plug := ivar
     and type bvar_plug := bvar) =

  struct

    module D' = D.F(Cut_gen_access)

    include Types
    include Types_uf
    include Access

    let register_var {r_cch} v =
      let r_cch = Option.value_exn ~here:_here_ r_cch in
      cc_handler_catch_var_events r_cch v

    let register_ivar = register_var

    let register_bvar = register_var

    let make_cut_gen d_ctx ctx =
      make_cut_Gen (object
        method push_level =
          D'.push_level d_ctx ctx
        method backtrack =
          D'.backtrack d_ctx ctx
        method generate =
          match D'.generate d_ctx ctx (scip_null_sol ()) with
          | `Unknown ->
            SCIP_DIDNOTFIND
          | `Sat ->
            SCIP_FEASIBLE
          | `Unsat_Cut_Gen ->
            SCIP_SEPARATED
          | `Cutoff ->
            SCIP_CUTOFF
        method check =
          D'.check d_ctx ctx
      end)

    let make_ctx c =
      let r_ctx = assert_ok1 _here_ (sCIPcreate ())
      and r_cch = None
      and r_var_d = Dequeue.create ()
      and r_constraints_n = 0
      and r_has_objective = false
      and r_sol = None
      and r_cuts_n = 0 in
      let rval = {
        r_ctx;
        r_cch;
        r_var_d;
        r_constraints_n;
        r_has_objective;
        r_sol;
        r_cuts_n
      } in
      let o = Some (make_cut_gen c rval) in
      let r_cch = Some (new_cc_handler r_ctx None o) in
      rval.r_cch <- r_cch;
      cc_handler_include (Option.value_exn rval.r_cch ~here:_here_);
      assert_ok _here_ (sCIPincludeDefaultPlugins_modified r_ctx);
      assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
      run_config_list r_ctx;
      rval

  end

end
