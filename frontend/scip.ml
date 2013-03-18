open Core.Std
open Scip_idl

(*
module TBI = (Core.Std.Int64: Int_intf.S)
open TBI
*)

exception Int_Exn of string

type ctx = {
  r_ctx: scip;
  r_cch: cch;
  r_var_d: var option Dequeue.t;
  mutable r_constraints_n: int;
  mutable r_has_objective: bool;
  mutable r_sol: sol option;
}

type f = string

type var = Scip_idl.var

type named_constraint = cons

let string_of_retcode = function
  | SCIP_OKAY ->
    "SCIP_OKAY"
  | SCIP_ERROR ->
    "SCIP_ERROR"
  | SCIP_NOMEMORY ->
    "SCIP_NOMEMORY"
  | SCIP_READERROR ->
    "SCIP_READERROR"
  | SCIP_WRITEERROR ->
    "SCIP_WRITEERROR"
  | SCIP_NOFILE ->
    "SCIP_NOFILE"
  | SCIP_FILECREATEERROR ->
    "SCIP_FILECREATEERROR"
  | SCIP_LPERROR ->
    "SCIP_LPERROR"
  | SCIP_NOPROBLEM ->
    "SCIP_NOPROBLEM"
  | SCIP_INVALIDCALL ->
    "SCIP_INVALIDCALL"
  | SCIP_INVALIDDATA ->
    "SCIP_INVALIDDATA"
  | SCIP_INVALIDRESULT ->
    "SCIP_INVALIDRESULT"
  | SCIP_PLUGINNOTFOUND ->
    "SCIP_PLUGINNOTFOUND"
  | SCIP_PARAMETERUNKNOWN ->
    "SCIP_PARAMETERUNKNOWN"
  | SCIP_PARAMETERWRONGTYPE ->
    "SCIP_PARAMETERWRONGTYPE"
  | SCIP_PARAMETERWRONGVAL ->
    "SCIP_PARAMETERWRONG"
  | SCIP_KEYALREADYEXISTING ->
    "SCIP_KEYALREADYEXISTING"
  | SCIP_MAXDEPTHLEVEL ->
    "SCIP_MAXDEPTHLEVEL"

let assert_ok s = function
  | SCIP_OKAY ->
    ()
  | v ->
    let m =
      Printf.sprintf
        "%s returned %s" s (string_of_retcode v) in
    raise (Int_Exn m)

let string_of_version () =
  Printf.sprintf "%d.%d.%d"
    (sCIPmajorVersion ())
    (sCIPminorVersion ())
    (sCIPtechVersion ())

let new_ctx () =
  let k, r_ctx = sCIPcreate () in
  assert_ok "create" k;
  let r_cch = new_cc_handler r_ctx in
  cc_handler_include r_cch;
  let k = sCIPincludeDefaultPlugins r_ctx in
  assert_ok "includeDefaultPlugins" k;
  let k = sCIPcreateProbBasic r_ctx "prob" in
  assert_ok "createProb" k;
  let k = sCIPsetEmphasis r_ctx SCIP_PARAMEMPHASIS_EASYCIP true in
  assert_ok "setEmphasis" k;
  let k = sCIPsetIntParam r_ctx "display/verblevel" 0 in
  assert_ok "setIntParam" k;
  let r_var_d = Dequeue.create () ~dummy:None
  and r_constraints_n = 0
  and r_has_objective = false
  and r_sol = None in
  {r_ctx; r_cch; r_var_d; r_constraints_n; r_has_objective; r_sol}

let scip_lb {r_ctx} =
  Option.value_map
    ~default:(~-. (sCIPinfinity r_ctx))
    ~f:Int64.to_float

let scip_ub {r_ctx} =
  Option.value_map
    ~default:(sCIPinfinity r_ctx)
    ~f:Int64.to_float

let scip_lb_float {r_ctx} =
  Option.value ~default:(~-. (sCIPinfinity r_ctx))

let scip_ub_float {r_ctx} =
  Option.value ~default:(sCIPinfinity r_ctx)

let new_var ({r_ctx; r_var_d} as r) t =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let k, v =
    match t with
    | Expr.T_Int (lb, ub) ->
      sCIPcreateVarBasic
        r_ctx id (scip_lb r lb) (scip_ub r ub)
        0. SCIP_VARTYPE_INTEGER
    | Expr.T_Real (lb, ub) ->
      sCIPcreateVarBasic
        r_ctx id (scip_lb_float r lb) (scip_ub_float r ub)
        0. SCIP_VARTYPE_CONTINUOUS in
  assert_ok "createVar" k;
  let k = sCIPaddVar r_ctx v in
  assert_ok "addVar" k;
  Dequeue.push_back r_var_d (Some v); v

let iexpr_vars (l, o) =
  Array.of_list (List.map l ~f:snd)

let create_constraint ({r_ctx; r_constraints_n} as r) eq (l, o) =
  let k, c =
    sCIPcreateConsBasicLinear r_ctx
      (Printf.sprintf "c%d" r_constraints_n)
      (Array.of_list_map ~f:snd l)
      (Array.of_list_map ~f:(Fn.compose Int64.to_float fst) l)
      (-. (if eq then Int64.to_float o else sCIPinfinity r_ctx))
      (Int64.to_float (Int64.neg o)) in
  assert_ok "createConsBasicLinear" k;
  r.r_constraints_n <- r_constraints_n + 1; c

let add_le ({r_ctx} as ctx) e =
  let c = create_constraint ctx false e in
  let k = sCIPaddCons r_ctx c in
  assert_ok "addCons" k

let add_eq ({r_ctx} as ctx) e =
  let c = create_constraint ctx true e in
  let k = sCIPaddCons r_ctx c in
  assert_ok "addCons" k

let add_call {r_cch} (v, o) f l =
  Scip_idl.cc_handler_call r_cch v o f
    (Array.of_list_map l ~f:fst)
    (Array.of_list_map l ~f:snd)

let add_objective {r_ctx; r_has_objective; r_var_d} l =
  if r_has_objective then
    raise (Int_Exn "problem already has objective")
  else
    List.iter l
      ~f:(fun (c, v) ->
        assert_ok "chgVarObj"
          (sCIPchgVarObj r_ctx v (Int64.to_float c)))

let result_of_status = function
  | SCIP_STATUS_OPTIMAL ->
    Expr.R_Opt
  | SCIP_STATUS_UNBOUNDED ->
    Expr.R_Unbounded
  | SCIP_STATUS_INFEASIBLE ->
    Expr.R_Unsat
  | _ ->
    Expr.R_Unknown

let write_ctx {r_ctx} filename =
  let k = sCIPwriteOrigProblem r_ctx filename "lp" false in
  assert_ok "writeOrigProblem" k

let solve ({r_ctx} as r) =
  let k = sCIPsolve r_ctx in
  assert_ok "solve" k;
  let rval = result_of_status (sCIPgetStatus r_ctx) in
  (match rval with
  | Expr.R_Opt | Expr.R_Unbounded | Expr.R_Sat ->
    r.r_sol <- Some (sCIPgetBestSol r_ctx)
  | _ -> ());
  rval

let assignment {r_ctx; r_var_d; r_sol} i =
  Option.map2 r_sol (Dequeue.get_exn r_var_d i)
    ~f:(sCIPgetSolVal r_ctx)

let variables_number {r_var_d} = Dequeue.length r_var_d

let constraints_number {r_constraints_n} = r_constraints_n
