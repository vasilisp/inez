open Core.Std
open Db_lang_abstract

module Make

  (I : Lang_ids.S)
  (F : functor (S : Lang_ids.S) -> Solver_intf.S) =

struct

  (* 2nd namespace; to be used for dummy variables *)
  module I' = Lang_ids.Make (struct end)

  module C  =  Lang_abstract.Make_term_conv(M)(Lang_abstract.M)

  type int_id = (I.c, int) Lang_ids.t
  
  type bool_id = (I.c, bool) Lang_ids.t

  type int_id'' = (I.c, int) Lang_ids.t

  type bool_id'' = (I.c, bool) Lang_ids.t

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

  let hashable_bool_id'' = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Lang_ids.compare I.compare_c Bool.compare;
    sexp_of_t = Lang_ids.sexp_of_t I.sexp_of_c Bool.sexp_of_t
  }

  type in_constraint =
    In : (I.c, 's) R.t * (I.c, 's) R.t list -> in_constraint

  type ctx = {
    r_int_id_m   :  (int_id, int_id'') Hashtbl.t;
    r_bool_id_m  :  (bool_id, int_id'') Hashtbl.t;
    r_in_m       :  (bool_id'', in_constraint list) Hashtbl.t;
  }

  let make_ctx () = {
    r_int_id_m = 
      Hashtbl.create () ~size:10240 ~hashable:hashable_int_id;
    r_bool_id_m = 
      Hashtbl.create () ~size:10240 ~hashable:hashable_bool_id;
    r_in_m = 
      Hashtbl.create () ~size:10240 ~hashable:hashable_bool_id''

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
  type s . ('c, s) D.t -> bool =
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

  let rec purify_membership :
  type s . ?acc:(in_constraint list) -> ctx ->
    (I.c, s) D.t -> (I.c, s) R.t ->
    in_constraint list * I.c Lang_abstract.A.t Formula.t =
    fun ?acc:(acc = []) x d r ->
      match d, r with
      | D.D_Input (_, l), _ ->
        In (r, l) :: acc, Formula.true'
      | D.D_Cross (d1, d2), R.R_Pair (r1, r2) ->
        let acc, g1 = purify_membership ~acc x d1 r1 in
        let acc, g2 = purify_membership ~acc x d2 r2 in
        acc, Formula.(g1 && g2)
      | D.D_Sel (d, f), _ ->
        let g1 = purify_formula x (f r) in
        let acc, g2 = purify_membership ~acc x d r in
        acc, Formula.(g1 && g2)

  and purify_atom =
    let fv = {Lang_ids.f_id = Fn.id} in
    fun x -> function
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

end
