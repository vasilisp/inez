open Core.Std

open Lang_abstract

module L = Smtlib_lexer

exception Smtlib_exn of string

(* 

   We first translate sequences of tokens to S-expressions.

*)

type smtlib_sexp =
  S_List of smtlib_sexp list
| S_Atom of Smtlib_lexer.token'

type ctx = {
  r_ctx  :  Smtlib_lexer.ctx;
  r_buf  :  Lexing.lexbuf;
}

let make_ctx b = {
  r_ctx  =  L.make_ctx ();
  r_buf  =  b;
}

let get_token {r_ctx; r_buf} =
  L.token r_ctx r_buf

let rec get_smtlib_sexp_list r ~acc =
  match get_token r with
  | L.T_RParen ->
    List.rev acc
  | token ->
    let acc = get_smtlib_sexp r ~token :: acc in
    get_smtlib_sexp_list r ~acc

and get_smtlib_sexp ?token r =
  let token =
    match token with
    | Some token ->
      token
    | None ->
      get_token r in
  match token with
  | L.T_LParen ->
    S_List (get_smtlib_sexp_list r ~acc:[])
  | L.T_RParen ->
    raise (Smtlib_exn "unmatched parentheses")
  | L.T_Other k ->
    S_Atom k

(*

  We now translate smtlib_sexp to our GADT representation. Leaving the
  bulk out of the functor (for now).

*)

type 'c ibterm =
  (('c, int) term, 'c atom formula) Lang_types.ibeither

type 'c tbox = 'c term_box

type 'c map = {
  m_find     :  string -> 'c tbox option;
  m_replace  :  string -> 'c tbox -> 'c map;
  m_type     :  't . ('c, 't) term -> 't Lang_types.t
}

  (* utilities *)

let lbx x = Box x

let tbx x = Lang_types.Box x

let term_of_formula = function
  | F_Atom (A_Bool t) ->
    t
  | t ->
    M_Bool t

let sum ~f =
  (List.fold_left
     ~init:zero
     ~f:(fun acc x -> acc + f x))

let map_matching_types e1 e2 ~fi ~fb =
  Lang_types.(match e1, e2 with
  | H_Int e1, H_Int e2 ->
    fi e1 e2
  | H_Bool e1, H_Bool e2 ->
    fb e1 e2
  | _ ->
    raise (Smtlib_exn "type error"))

  (* parsing functions *)

let rec parse_nonlist {m_find; m_type} = function
  | L.K_Int i ->
    Lang_types.H_Int (M_Int i)
  | L.K_Symbol "true" ->
    Lang_types.H_Bool F_True
  | L.K_Symbol "false" ->
    Lang_types.H_Bool (F_Not F_True)
  | L.K_Symbol s ->
    (match m_find s with
    | None ->
      raise (Smtlib_exn "unknown id")
    | Some (Box e) ->
      match m_type e with
      | Lang_types.Y_Int ->
        Lang_types.H_Int e
      | Lang_types.Y_Bool ->
        Lang_types.H_Bool (F_Atom (A_Bool e))
      | _ ->
        raise (Smtlib_exn (Printf.sprintf "%s is a function" s)))
  | _ ->
    raise (Smtlib_exn "syntax error")

let rec parse_let init l e =
  let m =
    List.fold_left l ~init
      ~f:(fun {m_replace; m_type} -> function
      | S_List [S_Atom (L.K_Symbol id); e] ->
        (match parse init e with
        | Lang_types.H_Int e ->
          m_replace id (lbx e)
        | Lang_types.H_Bool e ->
          m_replace id (lbx (term_of_formula e)))
      | _ ->
        raise (Smtlib_exn "syntax error")) in
  parse m e

and parse_int m e =
  match (parse m e : 'c ibterm) with
  | Lang_types.H_Int i ->
    i
  | Lang_types.H_Bool _ ->
    raise (Smtlib_exn "type error: int expected")

and parse_bool m e =
  match parse m e with
  | Lang_types.H_Bool b ->
    b
  | Lang_types.H_Int _ ->
    raise (Smtlib_exn "type error: bool expected")

and parse_eq m e1 e2 =
  map_matching_types (parse m e1) (parse m e2)
    ~fi:(fun e1 e2 -> F_Atom (A_Eq (e1 - e2)))
    ~fb:(fun e1 e2 -> (e1 => e2) && (e2 => e1))

and parse_app :
type t . 'c map -> ('c, t) term -> t Lang_types.t ->
  smtlib_sexp list -> 'c ibterm =
  fun m f t l ->
    match t, l with
      (* base cases *)
    | Lang_types.Y_Int, [] ->
      Lang_types.H_Int f
    | Lang_types.Y_Bool, [] ->
      Lang_types.H_Bool (F_Atom (A_Bool f))
      (* erroneous base cases *)
    | Lang_types.Y_Int, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Lang_types.Y_Bool, _ ->
      raise (Smtlib_exn "wrong number of arguments")
      (* recursive cases *)
    | Lang_types.Y_Int_Arrow t, a :: l ->
      let a = parse_int m a in
      parse_app m (M_App (f, a)) t l
    | Lang_types.Y_Bool_Arrow t, a :: l ->
      let a = parse_bool m a in
      parse_app m (M_App (f, term_of_formula a)) t l
      (* erroneous recursive cases *)
    | Lang_types.Y_Int_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")
    | Lang_types.Y_Bool_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")

and parse m = function
  | S_Atom k ->
    parse_nonlist m k
  | S_List [S_Atom L.K_Let; S_List l; e] ->
    parse_let m l e
    (* int cases *)
  | S_List (S_Atom L.K_Symbol "+" :: args) ->
    Lang_types.H_Int (sum args ~f:(parse_int m))
    (* bool cases *)
  | S_List (S_Atom L.K_Symbol "and" :: args) ->
    Lang_types.H_Bool (forall args ~f:(parse_bool m))
  | S_List (S_Atom L.K_Symbol "or" :: args) ->
    Lang_types.H_Bool (exists args ~f:(parse_bool m))
  | S_List (S_Atom L.K_Symbol "=>" :: args) ->
    (match List.rev args with
    | a :: d ->
      let init = parse_bool m a
      and f acc e = parse_bool m e => acc in
      Lang_types.H_Bool (List.fold_left d ~init ~f)
    | _ ->
      raise (Smtlib_exn "syntax error"))
  | S_List [S_Atom L.K_Symbol "not"; e] ->
    Lang_types.H_Bool (not (parse_bool m e))
    (* polymorphic cases *)
  | S_List [S_Atom L.K_Symbol "ite"; e1; e2; e3] ->
    let e1 = parse_bool m e1 in
    map_matching_types (parse m e2) (parse m e3)
      ~fi:(fun e2 e3 -> Lang_types.H_Int (M_Ite (e1, e2, e3)))
      ~fb:(fun e2 e3 -> Lang_types.H_Bool (F_Ite (e1, e2, e3)))
  | S_List [S_Atom L.K_Symbol "="; e1; e2] ->
    Lang_types.H_Bool (parse_eq m e1 e2)
  | S_List [S_Atom L.K_Symbol "distinct"; e1; e2] ->
    Lang_types.H_Bool (F_Not (parse_eq m e1 e2))
  | _ ->
    raise (Smtlib_exn "syntax error")
