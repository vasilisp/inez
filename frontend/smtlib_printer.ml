open Core.Std
open Terminology
open Core.Int_replace_polymorphic_compare

module Make (I : Id.Accessors) = struct

  open Logic

  type formula = I.c A.t Formula.t

  let hashable_idbox = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Id.Box.compare I.compare_c;
    sexp_of_t = Id.Box.sexp_of_t I.sexp_of_c
  }

  type ctx = {
    r_constraints       :  formula Dequeue.t;
    r_ids               :  (I.c Id.Box.t, int) Hashtbl.t;
    mutable r_ids_next  :  int;
  }

  let make_ctx () = {
    r_constraints  =  Dequeue.create ();
    r_ids          =  Hashtbl.create () ~hashable:hashable_idbox;
    r_ids_next     =  0
  }

  let rec register_ids_term :
  type s . ctx -> (I.c, s) M.t -> unit =
    fun ({r_ids; r_ids_next} as r) -> function
    | M.M_Bool g ->
      register_ids_formula r g
    | M.M_Int _ ->
      ()
    | M.M_Sum (s, t) ->
      register_ids_term r s;
      register_ids_term r t
    | M.M_Prod (_, s) ->
      register_ids_term r s
    | M.M_Ite (c, s, t) ->
      register_ids_formula r c;
      register_ids_term r s;
      register_ids_term r t
    | M.M_App (f, t) ->
      register_ids_term r f;
      register_ids_term r t
    | M.M_Var id ->
      let default () =
        let c = r_ids_next in
        r.r_ids_next <- c + 1;
        c in
      ignore (Hashtbl.find_or_add r_ids (Id.Box.Box id) ~default)
      
  and register_ids_atom r a ~polarity =
    match a with
    | A.A_Bool b ->
      register_ids_term r b
    | A.A_Le i | A.A_Eq i ->
      register_ids_term r i

  and register_ids_formula r g =
    let f = register_ids_atom r and polarity = `Both in
    Formula.iter_non_atomic g ~f ~polarity

  let assert_formula ({r_constraints} as r) g =
    register_ids_formula r g;
    Dequeue.enqueue_back r_constraints g

  let rec args_and_ret_of_type :
  type s . acc:Type.ibtype list ->
    s Type.t -> Type.ibtype list * Type.ibtype =
    fun ~acc -> function
    | Type.Y_Int ->
      List.rev acc, Type.E_Int
    | Type.Y_Bool ->
      List.rev acc, Type.E_Bool
    | Type.Y_Int_Arrow y ->
      let acc = Type.E_Int :: acc in
      args_and_ret_of_type ~acc y
    | Type.Y_Bool_Arrow y ->
      let acc = Type.E_Bool :: acc in
      args_and_ret_of_type ~acc y

  let string_of_ibtype =
    let i = "Int" and b = "Bool" in
    function
    | Type.E_Int -> i
    | Type.E_Bool -> b

  let pp_id ~key:(Id.Box.Box id) ~data =
    let y = I.type_of_t id in
    let l, r = args_and_ret_of_type [] y in
    let l = List.map l ~f:string_of_ibtype
    and r = string_of_ibtype r in
    let s_l = String.concat l ~sep:" " in
    Printf.printf "(declare-fun s%d (%s) %s)\n" data s_l r

  let pp_ids {r_ids} =
    Hashtbl.iter r_ids ~f:pp_id

  let string_of_id {r_ids} id =
    Printf.sprintf "c%d"
      (Option.value_exn ~here:_here_
         (Hashtbl.find r_ids (Id.Box.Box id)))

  let rec id_and_strings_of_app :
  type s t . ctx ->
    (I.c, s -> t) M.t -> acc:string list -> string * string list =
    fun r s ~acc ->
      match s with
      | M.M_Var id ->
        string_of_id r id, List.rev acc
      | M.M_App (f, s) ->
        let acc = string_of_term r s :: acc in
        id_and_strings_of_app r f ~acc

  and string_of_term :
  type s . ctx -> (I.c, s) M.t -> string =
    fun ({r_ids} as r) -> function
    | M.M_Bool g ->
      string_of_formula r g
    | M.M_Int x ->
      Int63.to_string x
    | M.M_Sum (s, t) ->
      Printf.sprintf "(+ %s %s)"
        (string_of_term r s)
        (string_of_term r t)
    | M.M_Prod (x, s) ->
      Printf.sprintf "(* %s %s)"
        (Int63.to_string x)
        (string_of_term r s)
    | M.M_Ite (c, s, t) ->
      Printf.sprintf "(ite %s %s %s)"
        (string_of_formula r c)
        (string_of_term r s)
        (string_of_term r t)
    | M.M_App (f, s) ->
      let acc = [string_of_term r s] in
      let id, l = id_and_strings_of_app r f ~acc in
      Printf.sprintf "(%s %s)" id (String.concat l ~sep:" ")
    | M.M_Var id ->
      string_of_id r id

  and string_of_atom r = function
    | A.A_Bool b ->
      string_of_term r b
    | A.A_Le s ->
      Printf.sprintf "(<= %s 0)" (string_of_term r s)
    | A.A_Eq s ->
      Printf.sprintf "(= %s 0)" (string_of_term r s)

  and string_of_formula r = function
    | Formula.F_True ->
      "true"
    | Formula.F_Atom a ->
      string_of_atom r a
    | Formula.F_Not g ->
      Printf.sprintf "(not %s)" (string_of_formula r g)
    | Formula.F_And (g, h) ->
      Printf.sprintf "(and %s %s)"
        (string_of_formula r g)
        (string_of_formula r h)
    | Formula.F_Ite (c, g, h) ->
      Printf.sprintf "(ite %s %s %s)"
        (string_of_formula r c)
        (string_of_formula r g)
        (string_of_formula r h)

  let pp_constraint r g =
    print_endline (string_of_formula r g)

  let pp_constraints ({r_constraints} as r) =
    Dequeue.iter r_constraints ~f:(pp_constraint r)

  let solve r =
    pp_ids r;
    pp_constraints r

end
