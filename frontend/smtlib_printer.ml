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

  let print_declaration oc ~key:(Id.Box.Box id) ~data =
    Printf.fprintf oc "(declare-fun c%d (" data;
    let y = I.type_of_t id in
    let l, r = args_and_ret_of_type [] y in
    (let f = Fn.compose (output_string oc) string_of_ibtype in
     List.iter l ~f);
    Printf.fprintf oc " ) %s)\n" (string_of_ibtype r)

  let print_declarations oc {r_ids} =
    Hashtbl.iter r_ids ~f:(print_declaration oc)

  let print_id oc {r_ids} id =
    Printf.fprintf
      oc "c%d "
      (Option.value_exn ~here:_here_
         (Hashtbl.find r_ids (Id.Box.Box id)))

  let print_int63 oc x =
    let open Int63 in
    if x < zero then
      Printf.fprintf oc "(- %s) " (Int63.to_string (- x))
    else
      Printf.fprintf oc "%s " (Int63.to_string x)

  let rec iter_conjunction g ~f =
    match g with
    | Formula.F_And (a, b) ->
      iter_conjunction a ~f;
      iter_conjunction b ~f
    | _ ->
      f g 

  let rec print_app_aux :
  type s t . out_channel -> ctx -> (I.c, s -> t) M.t -> unit =
    fun oc r s ->
      match s with
      | M.M_Var id ->
        print_id oc r id
      | M.M_App (f, s) ->
        print_app_aux oc r f;
        (* FIXME *)
        print_term oc r s

  and print_term :
  type s . out_channel -> ctx -> (I.c, s) M.t -> unit =
    fun oc ({r_ids} as r) -> function
    | M.M_Bool g ->
      print_formula oc r g
    | M.M_Int x ->
      print_int63 oc x
    | M.M_Sum (s, t) ->
      output_string oc "(+ ";
      print_term oc r s;
      print_term oc r t;
      output_string oc ") "
    | M.M_Prod (x, s) ->
      output_string oc "(* ";
      print_int63 oc x;
      print_term oc r s;
      output_string oc ") ";
    | M.M_Ite (c, s, t) ->
      output_string oc "(ite ";
      print_formula oc r c;
      print_term oc r s;
      print_term oc r t;
      output_string oc ") "
    | M.M_App (f, s) ->
      output_string oc "(";
      print_app_aux oc r f;
      print_term oc r s;
      output_string oc ") "
    | M.M_Var id ->
      print_id oc r id

  and print_atom oc r = function
    | A.A_Bool b ->
      print_term oc r b
    | A.A_Le s ->
      output_string oc "(<= ";
      print_term oc r s;
      output_string oc " 0) "
    | A.A_Eq s ->
      output_string oc "(= ";
      print_term oc r s;
      output_string oc " 0) "

  and print_formula oc r = function
    | Formula.F_True ->
      output_string oc "true "
    | Formula.F_Atom a ->
      print_atom oc r a
    | Formula.F_Not g ->
      output_string oc "(not ";
      print_formula oc r g;
      output_string oc ") "
    | Formula.F_And (_, _) as g ->
      output_string oc "(and ";
      iter_conjunction g ~f:(print_formula oc r);
      output_string oc ") "
    | Formula.F_Ite (c, g, h) ->
      output_string oc "(ite ";
      print_formula oc r c;
      print_formula oc r g;
      print_formula oc r h;
      output_string oc ") "

  let print_constraint oc r g =
    output_string oc "(assert ";
    print_formula oc r g;
    output_string oc ")\n"

  let print_constraints oc ({r_constraints} as r) =
    Dequeue.iter r_constraints ~f:(print_constraint oc r)

  let solve r =
    print_declarations stdout r;
    print_constraints stdout r;
    print_endline "(check-sat)"

end
