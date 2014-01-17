open Core.Std
open Db_logic

let fold_cross_product l1 l2 ~f ~init =
  List.fold_left l1 ~init
    ~f:(fun init x ->
      List.fold_left l2 ~f:(fun init y -> f init x y) ~init)

module Make (Imt : Imt_intf.S_access) (I : Id.S) = struct
    
  module C =  Logic.Make_term_conv(M)(Logic.M)

  module S = Solver.Make(Imt)(I)

  include S

  type polarity = [ `Positive | `Negative | `Both ]

  (* type ctx = S.ctx *)
  
  let fv = {Id.f_id = Fn.id}

  let rec overapproximate_db :
  type s .
  (I.c, s) D.t -> ((I.c, s) R.t * I.c Db_logic.A.t Formula.t) list =
    function
    | D.D_Input (_, l) ->
      List.map l ~f:(fun r -> r, Formula.F_True)
    | D.D_Cross (a, b) ->
      let a = overapproximate_db a
      and b = overapproximate_db b
      and f acc (r1, g1) (r2, g2) =
        match Formula.(g1 && g2) with
        | Formula.F_Not Formula.F_True ->
          acc
        | g ->
          (R.R_Pair (r1, r2), g) :: acc in
      fold_cross_product a b ~init:[] ~f
    | D.D_Sel (D.D_Cross (a, b), f) ->
      let a = overapproximate_db a
      and b = overapproximate_db b
      and f acc (r1, g1) (r2, g2) =
        match Formula.(g1 && g2 && f (R.R_Pair (r1, r2))) with
        | Formula.F_Not Formula.F_True ->
          acc
        | g ->
          (R.R_Pair (r1, r2), g) :: acc in
      fold_cross_product a b ~init:[] ~f
    | D.D_Sel (d, f) ->
      let f acc (r, g) =
        match Formula.(g && f r) with
        | Formula.F_Not Formula.F_True ->
          acc
        | g ->
          (r, g) :: acc in
      List.fold_left (overapproximate_db d) ~f ~init:[]

  and blast_existential :
  type s . (I.c, s) D.t -> polarity:polarity ->
    I.c Logic.A.t Formula.t =
    fun d ~polarity ->
      let f (_, g) = purify_formula g ~polarity in
      Formula.exists (overapproximate_db d) ~f

  and purify_atom a ~polarity =
    match a with
    | A.A_Exists d ->
      blast_existential d ~polarity
    | A.A_Bool b ->
      Formula.F_Atom 
        (Logic.A.A_Bool
           (C.map_non_atomic b ~f:purify_atom ~fv))
    | A.A_Le e ->
      Formula.F_Atom 
        (Logic.A.A_Le
           (C.map_non_atomic e ~f:purify_atom ~fv))
    | A.A_Eq e ->
      Formula.F_Atom 
        (Logic.A.A_Eq
           (C.map_non_atomic e ~f:purify_atom ~fv))

  and purify_formula ~polarity =
    Formula.map_non_atomic ~f:purify_atom ~polarity

  let assert_formula r g =
    let g = purify_formula g ~polarity:`Positive in
    assert_formula r g

  let add_objective r o =
    let o = C.map_non_atomic o ~f:purify_atom ~fv in
    add_objective r o

end
