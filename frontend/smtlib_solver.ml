open Core.Std
open Terminology
open Lang_abstract

type 'c tbox = 'c Box.t

module R = struct

  type 'r t = P_Ok of 'r | P_Unsupported | P_Syntax | P_Type | P_Bug

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

  (S : Solver_intf.S_unit_creatable)
  (I : Lang_ids.S with type c = S.c) =

struct

  open Smtlib_parser
  
  module L = Smtlib_lexer

  type logic = Q_Lia | Q_Uflia | Q_Idl | Q_Ufidl

  type status = K_Sat | K_Unsat

  type ctx = {
    mutable r_logic       :  logic option;
    mutable r_status      :  status option;
    mutable r_sat_called  :  bool;
    mutable r_map         :  S.c Box.t String.Map.t;
    r_ctx                 :  S.ctx;
  }

  let tbx x = Lang_types.Box.Box x

  let lbx x = Box.Box x

  let rec make_env m =
    let e_find = String.Map.find m
    and e_replace key data = make_env (String.Map.add m ~key ~data)
    and e_type = M.type_of_t ~f:I.type_of_t' in
    {e_find; e_replace; e_type}

  let make_ctx r_ctx = {
    r_logic       =  None;
    r_status      =  None;
    r_sat_called  =  false;
    r_map         =  String.Map.empty;
    r_ctx
  }

  let check_logic ({r_logic} as r) s x =
    match r_logic, s with
    | Some _, _ ->
      R.P_Syntax
    | None, "QF_LIA" ->
      r.r_logic <- Some Q_Lia;
      R.P_Ok x
    | None, "QF_UFLIA" ->
      r.r_logic <- Some Q_Uflia;
      R.P_Ok x
    | None, "QF_IDL" ->
      r.r_logic <- Some Q_Idl;
      R.P_Ok x
    | None, "QF_UFIDL" ->
      r.r_logic <- Some Q_Ufidl;
      R.P_Ok x
    | _ ->
      R.P_Unsupported

  let check_status ({r_status} as r) s x =
    match r_status, s with
    | Some _, _ ->
      R.P_Syntax
    | None, "sat" ->
      r.r_status <- Some K_Sat;
      R.P_Ok x
    | None, "unsat" ->
      r.r_status <- Some K_Unsat;
      R.P_Ok x
    | None, _ ->
      R.P_Syntax

  let check_result {r_status} e =
    match r_status, e with
    | Some K_Sat, R_Unsat ->
      R.P_Bug
    | Some K_Unsat, (R_Opt  | R_Unbounded | R_Sat) ->
      R.P_Bug
    | _ ->
      R.P_Ok (Some e)

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
      let init = Lang_types.Box.t_of_ibtype init in
      Util.foldo_right l ~init
        ~f:(fun x (Lang_types.Box.Box acc) ->
          let f = function
            | Lang_types.E_Int ->
              tbx (Lang_types.Y_Int_Arrow acc)
            | _ ->
              tbx (Lang_types.Y_Bool_Arrow acc) in
          Option.map (type_of_sexp x) ~f)

  let parse_declare_fun ({r_map} as r) key l t =
    match type_of l t with
    | Some (Lang_types.Box.Box data) ->
      let data = lbx (M.M_Var (I.gen_id data)) in
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
    | [S_Atom L.K_Set_Info; S_Atom L.K_Key "status";
       S_Atom L.K_Symbol s] ->
      check_status r s None
    | [S_Atom L.K_Set_Info; S_Atom L.K_Key _; _] ->
      R.P_Ok None
    | [S_Atom L.K_Check_Sat] when r.r_sat_called ->
      R.P_Unsupported
    | [S_Atom L.K_Check_Sat] ->
      r.r_sat_called <- true;
      check_result r (S.solve r_ctx)
    | [S_Atom L.K_Declare_Fun; S_Atom L.K_Symbol id; S_List l; t] ->
      parse_declare_fun r id l t
    | [S_Atom L.K_Assert; c] ->
      (match parse (make_env r_map) c with
      | H_Int _ ->
        R.P_Type
      | H_Bool c ->
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
    | End_of_file ->
      ()

end
