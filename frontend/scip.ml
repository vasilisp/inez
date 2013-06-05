open Core.Std
open Scip_idl
open Terminology

exception Scip_Exn of (Here.t * retcode)

external address_of_value: 'a -> int = "address_of_value"

(* implementation first, then wrapping things up in modules and
   functors *)

type scip_ctx = {
  r_ctx: scip;
  r_var_d: var Dequeue.t;
  mutable r_cch: cch option;
  mutable r_constraints_n: int;
  mutable r_has_objective: bool;
  mutable r_sol: sol option;
}

let dummy_f = ""

let dummy_var = cc_handler_zero_var ()

type var = Scip_idl.var

let compare_var x y =
  Int.compare (address_of_value x) (address_of_value y)

let hash_var = address_of_value

let sexp_of_var v =
  Int.sexp_of_t (address_of_value v)

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
  _here_,
  (fun c -> sCIPsetEmphasis c SCIP_PARAMEMPHASIS_EASYCIP true);
  _here_,
  (fun c -> sCIPsetIntParam c "display/verblevel" 0);
  _here_,
  (fun c -> sCIPsetPresolving c SCIP_PARAMSETTING_OFF true);
]

let run_config_list c =
  List.iter config_list ~f:(fun (h, f) -> assert_ok h (f c))

let make_ctx () =
  let r_ctx = assert_ok1 _here_ (sCIPcreate ()) in
  let r_cch = Some (new_cc_handler r_ctx None) in
  cc_handler_include (Option.value_exn r_cch ~here:_here_);
  assert_ok _here_ (sCIPincludeDefaultPlugins r_ctx);
  assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
  run_config_list r_ctx;
  let r_var_d = Dequeue.create () ~dummy:dummy_var
  and r_constraints_n = 0
  and r_has_objective = false
  and r_sol = None in
  {r_ctx; r_cch; r_var_d; r_constraints_n; r_has_objective; r_sol}

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
  Dequeue.push_back r_var_d v; v

let new_bvar {r_ctx; r_var_d} =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (sCIPcreateVarBasic r_ctx id 0.0 1.0 0. SCIP_VARTYPE_BINARY) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.push_back r_var_d v; v

let negate_bvar {r_ctx; r_var_d} v =
  let v = assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v) in
  Dequeue.push_back r_var_d v; v

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
       (Array.of_list_map ~f:(Fn.compose Int63.to_float fst) l)
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
         (Array.of_list_map ~f:(Fn.compose Int63.to_float fst) l)
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
    (Array.of_list_map l ~f:(Fn.compose (var_of_var_option r) fst))
    (Array.of_list_map l ~f:(Fn.compose Int63.to_int64 snd))

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
  sCIPgetSolVal r_ctx sol v > 0.5

let ideref ({r_sol} as r) v =
  Option.map r_sol ~f:(fun s -> ideref_sol r s v)

let bderef ({r_sol} as r) v =
  Option.map r_sol ~f:(fun s -> bderef_sol r s v)

let branch {r_ctx} v x =
  let r, _, _, _ = sCIPbranchVarVal r_ctx v x in
  ok_or_fail_of_retcode r  

let variables_number {r_var_d} = Dequeue.length r_var_d

let constraints_number {r_constraints_n} = r_constraints_n

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
  let solve = solve
  let ideref = ideref
  let bderef = bderef
  let write_ctx = write_ctx
end

module Dp_access = struct

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

  let ibranch = branch

  let bbranch r v = branch r v 0.5

  let name_diff r v1 v2 =
    let v = new_ivar r (T_Int (None, None)) in
    Int63.(add_eq r [one, v1; minus_one, v2; minus_one, v] zero);
    Some v

  let ideref_sol = ideref_sol

  let bderef_sol = bderef_sol

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

    let result_of_response = function
      | N_Ok -> SCIP_DIDNOTFIND
      | N_Unsat -> SCIP_CUTOFF
      | N_Tightened -> SCIP_REDUCEDDOM

    let make_dp d_ctx ctx =
      make_dP (object
        method push_level =
          D'.push_level d_ctx ctx
        method backtrack =
          D'.backtrack d_ctx ctx
        method propagate =
          result_of_response (D'.propagate d_ctx ctx)
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
      and r_var_d = Dequeue.create () ~dummy:dummy_var
      and r_constraints_n = 0
      and r_has_objective = false
      and r_sol = None in
      let rval = {
        r_ctx;
        r_cch;
        r_var_d;
        r_constraints_n;
        r_has_objective;
        r_sol
      } in
      let o = Some (make_dp d rval) in
      let r_cch = Some (new_cc_handler r_ctx o) in
      rval.r_cch <- r_cch;
      cc_handler_include (Option.value_exn rval.r_cch ~here:_here_);
      assert_ok _here_ (sCIPincludeDefaultPlugins r_ctx);
      assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
      run_config_list r_ctx;
      rval
    
    let register _ _ _ = ()

  end

end
