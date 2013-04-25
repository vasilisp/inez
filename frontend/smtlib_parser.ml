open Core.Std
open Lang_abstract
open Lang_types

module L = Smtlib_lexer

exception Smtlib_exn of string

type smtlib_sexp =
  S_List of smtlib_sexp list
| S_Atom of Smtlib_lexer.token'

type ('b, 'i) binding =
  D_Sexp  of  smtlib_sexp
| D_Int   of  ('b, 'i, int) term
| D_Bool  of  ('b, 'i) atom formula
  
type ctx = {
  r_ctx  :  Smtlib_lexer.ctx;
  r_buf  :  Lexing.lexbuf;
  r_map  :  (int, int) binding String.Table.t
}

let make_ctx b = {
  r_ctx  =  L.make_ctx ();
  r_buf  =  b;
  r_map  =  String.Table.create ~size:1024 ()
}

let get_token {r_ctx; r_buf} =
  L.token r_ctx r_buf

let rec parse_list r ~acc =
  match get_token r with
  | L.T_RParen ->
    List.rev acc
  | token ->
    let acc = parse r ~token :: acc in
    parse_list r ~acc

and parse ?token r =
  let token =
    match token with
    | Some token ->
      token
    | None ->
      get_token r in
  match token with
  | L.T_LParen ->
    S_List (parse_list r ~acc:[])
  | L.T_RParen ->
    raise (Smtlib_exn "unmatched parentheses")
  | L.T_Other k ->
    S_Atom k

let term_of_formula = function
  | F_Atom (A_Bool t) ->
    t
  | t ->
    M_Bool t

let parse_let {r_map} l e ~f =
  let hidden =
    let f = function
      | S_List [S_Atom (L.K_Symbol id); e] ->
        let f o = Hashtbl.remove r_map id; id, o in
        Option.map (Hashtbl.find r_map id) ~f
      | _ ->
        raise (Smtlib_exn "syntax error") in
    List.filter_map l ~f
  and ids =
    let f = function
      | S_List [S_Atom (L.K_Symbol id); e] ->
        Hashtbl.replace r_map id (D_Sexp e); id
      | _ ->
        raise (Smtlib_exn "syntax error") in
    List.map l ~f in
  let r = f e in
  List.iter ids ~f:(Hashtbl.remove r_map);
  List.iter hidden ~f:(fun (id, o) -> Hashtbl.replace r_map id o);
  r

let rec parse_int_nonlist ({r_map} as r) = function
  | L.K_Int i ->
    M_Int i
  | L.K_Symbol s ->
    (match Hashtbl.find r_map s with
    | None ->
      raise (Smtlib_exn "unknown id")
    | Some (D_Int i) ->
      i
    | Some (D_Sexp e) ->
      let i = parse_int r e in
      Hashtbl.replace r_map s (D_Int i); i
    | Some (D_Bool _) ->
      raise (Smtlib_exn "int expected"))
  | _ ->
    raise (Smtlib_exn "syntax error")

and parse_bool_nonlist ({r_map} as r) = function
  | L.K_Symbol "true" ->
    F_True
  | L.K_Symbol "false" ->
    F_Not F_True
  | L.K_Symbol s ->
    (match Hashtbl.find r_map s with
    | None ->
      raise (Smtlib_exn "unknown id")
    | Some (D_Bool b) ->
      b
    | Some (D_Sexp e) ->
      let b = parse_bool r e in
      Hashtbl.replace r_map s (D_Bool b); b
    | Some (D_Int _) ->
      raise (Smtlib_exn "bool expected"))
  | _ ->
    raise (Smtlib_exn "syntax error")

and parse_int r = function
  | S_Atom k ->
    parse_int_nonlist r k
  | S_List [S_Atom L.K_Let; S_List l; e] ->
    parse_let r l e ~f:(parse_int r)
  | _ (* FIXME *) ->
    M_Int Int63.zero

and parse_bool r = function
  | S_Atom k ->
    parse_bool_nonlist r k
  | S_List [S_Atom L.K_Let; S_List l; e] ->
    parse_let r l e ~f:(parse_bool r)
  | _ (* FIXME *) ->
    F_True

and parse_int_app :
type t . ctx -> ('b, 'i, t) term -> t fun_type ->
  smtlib_sexp list -> ('b, 'i, int) term =
  fun r f t l ->
    match t, l with
    (* base cases *)
    | Y_Int_Arrow_Int, [a] ->
      let a = parse_int r a in
      M_App (f, a)
    | Y_Bool_Arrow_Int, [a] ->
      let a = parse_bool r a in
      M_App (f, term_of_formula a)
    (* erroneous base cases *)
    | Y_Int_Arrow_Int, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow_Int, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Int_Arrow_Bool, _ ->
      raise (Smtlib_exn "wrong return type")
    | Y_Bool_Arrow_Bool, _ ->
      raise (Smtlib_exn "wrong return type")
    (* recursive cases *)
    | Y_Int_Arrow t, a :: l ->
      let a = parse_int r a in
      parse_int_app r (M_App (f, a)) t l
    | Y_Bool_Arrow t, a :: l ->
      let a = parse_bool r a in
      parse_int_app r (M_App (f, term_of_formula a)) t l
    | Y_Int_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")

and parse_bool_app :
type t . ctx -> ('b, 'i, t) term -> t fun_type ->
  smtlib_sexp list -> ('b, 'i, bool) term =
  fun r f t l ->
    match t, l with
    (* base cases *)
    | Y_Int_Arrow_Bool, [a] ->
      let a = parse_int r a in
      M_App (f, a)
    | Y_Bool_Arrow_Bool, [a] ->
      let a = parse_bool r a in
      M_App (f, term_of_formula a)
    (* erroneous base cases *)
    | Y_Int_Arrow_Bool, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow_Bool, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Int_Arrow_Int, _ ->
      raise (Smtlib_exn "wrong return type")
    | Y_Bool_Arrow_Int, _ ->
      raise (Smtlib_exn "wrong return type")
    (* recursive cases *)
    | Y_Int_Arrow t, a :: l ->
      let a = parse_int r a in
      parse_bool_app r (M_App (f, a)) t l
    | Y_Bool_Arrow t, a :: l ->
      let a = parse_bool r a in
      parse_bool_app r (M_App (f, term_of_formula a)) t l
    | Y_Int_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")
