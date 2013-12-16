(* Our basic interface provides congruence closure but no interface
   for background decision procedures. *)
module Scip_basic : Imt_intf.S_unit_creatable

(* If [S_T] is a NO-style decision procedure for T, then
   [Scip_accepts_dp.Make(S_T)] is a decision procedure for ILP Modulo
   (CC + T). *)
module Scip_with_dp : Imt_intf.S_with_dp

module Scip_with_cut_gen : Imt_intf.S_with_cut_gen
