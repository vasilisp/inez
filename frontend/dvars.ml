open Core.Std
open Terminology

module Make

  (S : sig

    include Imt_intf.S_ivar

    include Imt_intf.S_int_bounds with type t := ivar

    val name_diff : ctx -> ivar -> ivar -> ivar option

  end) =

struct

  type ctx = S.ctx

  type sol = S.sol

  type t = S.ivar signed option offset
  with compare, sexp_of

  let create_dvar_base r v1 v2 =
    match v1, v2 with
    | Some v1, None ->
      Some (S_Pos v1)
    | None, Some v2 ->
      Some (S_Neg v2)
    | None, None ->
      None
    | Some v1, Some v2 when S.compare_ivar v1 v2 < 0 ->
      Option.(S.name_diff r v1 v2 >>| (fun v -> S_Pos v))
    | Some v1, Some v2 when S.compare_ivar v1 v2 > 0 ->
      Option.(S.name_diff r v2 v1 >>| (fun v -> S_Neg v))
    | Some v1, Some v2 ->
      None

  let create_dvar r (v1, o1) (v2, o2) =
    create_dvar_base r v1 v2, Int63.(o1 - o2)

  let get_lb_local_base r = function
    | Some (S_Pos v) ->
      S.get_lb_local r v
    | Some (S_Neg v) ->
      Option.(S.get_ub_local r v >>| Int63.(~-))
    | None ->
      Some Int63.zero

  let get_ub_local_base r = function
    | Some (S_Pos v) ->
      S.get_ub_local r v
    | Some (S_Neg v) ->
      Option.(S.get_lb_local r v >>| Int63.(~-))
    | None ->
      Some Int63.zero

  let ideref_sol_base r sol = function
    | Some (S_Pos v) ->
      S.ideref_sol r sol v
    | Some (S_Neg v) ->
      Int63.(- S.ideref_sol r sol v)
    | None ->
      Int63.zero

  let set_lb_local_base r v x =
    match v with
    | Some (S_Pos v) ->
      S.set_lb_local r v x
    | Some (S_Neg v) ->
      S.set_ub_local r v Int63.(- x)
    | None when Int63.(x <= zero) ->
      `Ok
    | None ->
      `Infeasible

  let set_ub_local_base r v x =
    match v with
    | Some (S_Pos v) ->
      S.set_ub_local r v x
    | Some (S_Neg v) ->
      S.set_lb_local r v Int63.(- x)
    | None when Int63.(x >= zero) ->
      `Ok
    | None ->
      `Infeasible

  let get_lb_local r (dv, o) =
    Option.(get_lb_local_base r dv >>| Int63.(+) o)

  let get_ub_local r (dv, o) =
    Option.(get_ub_local_base r dv >>| Int63.(+) o)

  let ideref_sol r sol (dv, o) =
    Int63.(ideref_sol_base r sol dv + o)

  let set_lb_local r (dv, o) x =
    set_lb_local_base r dv Int63.(x - o)

  let set_ub_local r (dv, o) x =
    set_ub_local_base r dv Int63.(x - o)

end
