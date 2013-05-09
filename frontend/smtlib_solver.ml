open Core.Std

type 'c tbox = 'c Lang_abstract.term_box

module R = struct

  type 'r t = P_Ok of 'r | P_Unsupported | P_Syntax | P_Type

  let map x ~f =
    match x with
    | P_Ok x ->
      P_Ok (f x)
    | _ ->
      x

  let map' x ~f =
    match x with
    | P_Ok x ->
      f x
    | _ ->
      x

end

module Make

  (S : Solver_intf.S) (I : Lang_ids.S with type c = S.c) =

struct

  open Smtlib_parser
  
  module L = Smtlib_lexer

  type logic = Q_Lia | Q_Uflia | Q_Idl | Q_Ufidl

  type ctx = {
    mutable r_logic       :  logic Set_once.t;
    mutable r_sat_called  :  bool;
    mutable r_map         :  S.c tbox String.Map.t;
    r_ctx                 :  S.ctx;
  }

  let tbx x = Lang_types.Box x

  let lbx x = Lang_abstract.Box x

  let rec make_env m =
    let e_find = String.Map.find m
    and e_replace key data = make_env (String.Map.add m ~key ~data)
    and e_type = Lang_abstract.type_of_term ~f:I.type_of_t' in
    {e_find; e_replace; e_type}

  let make_ctx r_ctx = {
    r_logic       =  Set_once.create ();
    r_sat_called  =  false;
    r_map         =  String.Map.empty;
    r_ctx
  }

  let check_logic {r_logic} s x =
    match Set_once.get r_logic, s with
    | Some _, _ ->
      R.P_Syntax
    | None, "QF_LIA" ->
      Set_once.set_exn r_logic Q_Lia;
      R.P_Ok x
    | None, "QF_UFLIA" ->
      Set_once.set_exn r_logic Q_Uflia;
      R.P_Ok x
    | None, "QF_IDL" ->
      Set_once.set_exn r_logic Q_Idl;
      R.P_Ok x
    | None, "QF_UFIDL" ->
      Set_once.set_exn r_logic Q_Ufidl;
      R.P_Ok x
    | _ ->
      R.P_Unsupported

  let type_of_sexp = function
    | S_Atom L.K_Symbol "Int" ->
      Some Lang_types.E_Int
    | S_Atom L.K_Symbol "Bool" ->
      Some Lang_types.E_Bool
    | _ ->
      None

  let type_of l t =
    match type_of_sexp t with
    | None ->
      None
    | Some init ->
      let init = Lang_types.t_box_of_ibtype init in
      Util.foldo_right l ~init
        ~f:(fun x (Lang_types.Box acc) ->
          let f = function
            | Lang_types.E_Int ->
              tbx (Lang_types.Y_Int_Arrow acc)
            | _ ->
              tbx (Lang_types.Y_Bool_Arrow acc) in
          Option.map (type_of_sexp x) ~f)

  let parse_declare_fun ({r_map} as r) key l t =
    match type_of l t with
    | Some (Lang_types.Box data) ->
      let data = lbx (Lang_abstract.M_Var (I.gen_id data)) in
      r.r_map <- String.Map.add r_map ~key ~data;
      R.P_Ok None
    | None ->
      R.P_Syntax

  let do_statement ({r_ctx; r_map} as r) = function
    | [S_Atom L.K_Set_Logic; S_Atom L.K_Symbol s] ->
      check_logic r s None
    | S_Atom
        (L.K_Push | L.K_Pop
            | L.K_Declare_Sort | L.K_Define_Sort | L.K_Define_Fun
            | L.K_Get_Assertions | L.K_Get_Proof | L.K_Get_Unsat_Core
            | L.K_Get_Option | L.K_Get_Info) :: _ ->
      R.P_Unsupported
    | [S_Atom L.K_Set_Option; S_Atom L.K_Key _; _] ->
      R.P_Ok None
    | [S_Atom L.K_Set_Info; S_Atom L.K_Key _; _] ->
      R.P_Ok None
    | [S_Atom L.K_Check_Sat] when r.r_sat_called ->
      R.P_Unsupported
    | [S_Atom L.K_Check_Sat] ->
      R.P_Ok (Some (S.solve r_ctx))
    | [S_Atom L.K_Declare_Fun; S_Atom L.K_Symbol id; S_List l; t] ->
      parse_declare_fun r id l t
    | [S_Atom L.K_Assert; c] ->
      (match parse (make_env r_map) c with
      | Lang_types.H_Int _ ->
        R.P_Type
      | Lang_types.H_Bool c ->
        S.assert_formula r_ctx c;
        R.P_Ok None)
    | [S_Atom L.K_Exit] ->
      exit 0
    | _ ->
      R.P_Syntax

  let rec do_statements r r' ~f ~f_err =
    match get_smtlib_sexp r with
    | S_List l ->
      f (do_statement r' l);
      do_statements r r' ~f ~f_err
    | S_Atom _ ->
      f_err ()

  let main channel ~f ~f_err =
    let r =  Smtlib_parser.make_ctx (Lexing.from_channel channel)
    and r' = make_ctx (S.make_ctx ()) in
    try
      do_statements r r' ~f ~f_err
    with
    | Smtlib_parser.Smtlib_Exn _ as e ->
      (Printf.printf "line: %d\n%!" (get_line r);
       raise e)

end
