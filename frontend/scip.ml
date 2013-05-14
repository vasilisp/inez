open Core.Std
open Scip_idl
open Terminology

exception Scip_Exn of (Here.t * retcode)

type ctx = {
  r_ctx: scip;
  r_cch: cch;
  r_var_d: var option Dequeue.t;
  mutable r_constraints_n: int;
  mutable r_has_objective: bool;
  mutable r_sol: sol option;
}

type f = string

let dummy_f = ""

(* type var = Scip_idl.var *)

type bvar = int

type ivar = int

let ivar_of_bvar x = x

(* TODO : check bounds *)
let bvar_of_ivar x = x

let sv {r_var_d} x =
  Option.value_exn (Dequeue.get_exn r_var_d x)

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

let string_of_version () =
  Printf.sprintf "%d.%d.%d"
    (sCIPmajorVersion ())
    (sCIPminorVersion ())
    (sCIPtechVersion ())

let config_list = [
  (fun c -> sCIPsetEmphasis c SCIP_PARAMEMPHASIS_EASYCIP true);
  (fun c -> sCIPsetIntParam c "display/verblevel" 0);
  (fun c -> sCIPsetPresolving c SCIP_PARAMSETTING_OFF true);
]

let run_config_list ctx =
  List.iter config_list
    ~f:Fn.(compose (assert_ok _here_) ((|>) ctx))

let new_ctx () =
  let r_ctx = assert_ok1 _here_ (sCIPcreate ()) in
  let r_cch = new_cc_handler r_ctx in
  cc_handler_include r_cch;
  assert_ok _here_ (sCIPincludeDefaultPlugins r_ctx);
  assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
  run_config_list r_ctx;
  let r_var_d = Dequeue.create () ~dummy:None
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
  Dequeue.push_back r_var_d (Some v); i

let new_bvar {r_ctx; r_var_d} =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (sCIPcreateVarBasic r_ctx id 0.0 1.0 0. SCIP_VARTYPE_BINARY) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.push_back r_var_d (Some v); i

let negate_bvar ({r_ctx; r_var_d} as r) v =
  let v = assert_ok1 _here_ (sCIPgetNegatedVar r_ctx (sv r v))
  and i = Dequeue.length r_var_d in
  Dequeue.push_back r_var_d (Some v); i

let iexpr_vars (l, o) =
  Array.of_list (List.map l ~f:snd)

let make_constraint_id ({r_constraints_n} as r) =
  let id = Printf.sprintf "c%d" r_constraints_n in
  r.r_constraints_n <- r_constraints_n + 1;
  id

let create_constraint ({r_ctx} as r) eq (l, o) =
  assert_ok1 _here_
    (sCIPcreateConsBasicLinear r_ctx
       (make_constraint_id r)
       (Array.of_list_map ~f:(Fn.compose (sv r) snd) l)
       (Array.of_list_map ~f:(Fn.compose Int63.to_float fst) l)
       (-. (if eq then Int63.to_float o else sCIPinfinity r_ctx))
       (Int63.to_float (Int63.neg o)))

let add_eq ({r_ctx} as r) e =
  let c = create_constraint r true e in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_le ({r_ctx} as r) e =
  let c = create_constraint r false e in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let var_of_var_signed ({r_ctx} as r) = function
  | S_Pos v ->
    sv r v
  | S_Neg v ->
    assert_ok1 _here_ (sCIPgetNegatedVar r_ctx (sv r v))

let add_indicator ({r_ctx} as r) v (l, o) =
  let c =
    assert_ok1 _here_
      (sCIPcreateConsBasicIndicator r_ctx
         (make_constraint_id r)
         (var_of_var_signed r v)
         (Array.of_list_map ~f:(Fn.compose (sv r) snd) l)
         (Array.of_list_map ~f:(Fn.compose Int63.to_float fst) l)
         (Int63.to_float (Int63.neg o))) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_clause ({r_ctx; r_constraints_n} as r) l =
  let c =
    assert_ok1 _here_
      (let l =
         Array.of_list_map l
           ~f:(function
           | S_Pos v -> sv r v
           | S_Neg v ->
             let k, v = sCIPgetNegatedVar r_ctx (sv r v) in
             assert_ok _here_ k; v) in
       sCIPcreateConsBasicLogicor r_ctx (make_constraint_id r) l) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let var_of_var_option ({r_cch} as r) =
  Option.value_map ~f:(sv r)
    ~default:(cc_handler_zero_var r_cch)

let add_call ({r_cch} as r) (v, o) f l =
  Scip_idl.cc_handler_call r_cch
    (var_of_var_option r v) (Int63.to_int64 o) f
    (Array.of_list_map l ~f:(Fn.compose (var_of_var_option r) fst))
    (Array.of_list_map l ~f:(Fn.compose Int63.to_int64 snd))

let add_objective ({r_ctx; r_has_objective} as r) l =
  if r_has_objective then
    `Duplicate
  else
    (List.iter l
       ~f:(fun (c, v) ->
         let c = Int63.to_float c in
         assert_ok _here_ (sCIPchgVarObj r_ctx (sv r v) c));
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
  cc_handler_finalize r_cch;
  assert_ok _here_ (sCIPsolve r_ctx);
  let rval = result_of_status (sCIPgetStatus r_ctx) in
  (match rval with
  | R_Opt | R_Unbounded | R_Sat ->
    r.r_sol <- Some (sCIPgetBestSol r_ctx)
  | _ -> ());
  rval

let ideref ({r_ctx; r_sol} as r) v =
  let f sol =
    let x = sCIPgetSolVal r_ctx sol (sv r v) in
    let i = Int63.of_float x in
    if Float.(x > Int63.to_float i + 0.5) then
      Int63.succ i
    else
      i in
  Option.map r_sol ~f

let bderef ({r_ctx; r_sol} as r) v =
  Option.map r_sol
    ~f:(fun r_sol -> sCIPgetSolVal r_ctx r_sol (sv r v) > 0.5)

let variables_number {r_var_d} = Dequeue.length r_var_d

let constraints_number {r_constraints_n} = r_constraints_n
