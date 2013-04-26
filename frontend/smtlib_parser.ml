open Core.Std
open Lang_abstract
open Lang_types

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

  We now translate smtlib_sexp to our GADT representation.

*)

type ('b, 'i) ibterm =
  (('b, 'i, int) term,
   ('b, 'i) atom formula) Lang_types.ibeither

(* utilities *)
  
let term_of_formula = function
  | F_Atom (A_Bool t) ->
    t
  | t ->
    M_Bool t

let sum ~f =
  List.fold_left ~init:zero
    ~f:(fun acc x -> acc + f x);;

let map_matching_types e1 e2 ~fi ~fb =
  match e1, e2 with
  | H_Int e1, H_Int e2 ->
    fi e1 e2
  | H_Bool e1, H_Bool e2 ->
    fb e1 e2
  | _ ->
    raise (Smtlib_exn "type error")

let rec parse_nonlist m = function
  | L.K_Int i ->
    H_Int (M_Int i)
  | L.K_Symbol "true" ->
    H_Bool F_True
  | L.K_Symbol "false" ->
    H_Bool (F_Not F_True)
  | L.K_Symbol s ->
    (match Map.find m s with
    | None ->
      raise (Smtlib_exn "unknown id")
    | Some e ->
      e)
  | _ ->
    raise (Smtlib_exn "syntax error")

let rec parse_let init l e =
  let m =
    List.fold_left l ~init
      ~f:(fun acc -> function
      | S_List [S_Atom (L.K_Symbol id); e] ->
        Map.add acc id (parse init e)
      | _ ->
        raise (Smtlib_exn "syntax error")) in
  parse m e

and parse_int m e =
  match parse m e with
  | H_Int i ->
    i
  | H_Bool _ ->
    raise (Smtlib_exn "type error: int expected")

and parse_bool m e =
  match parse m e with
  | H_Bool b ->
    b
  | H_Int _ ->
    raise (Smtlib_exn "type error: bool expected")

and parse_eq m e1 e2 =
  map_matching_types (parse m e1) (parse m e2)
    ~fi:(fun e1 e2 -> F_Atom (A_Eq (e1 - e2)))
    ~fb:(fun e1 e2 -> (e1 => e2) && (e2 => e1))

and parse_app :
type t . 'a String.Map.t -> ('b, 'i, t) term -> t fun_type ->
  smtlib_sexp list -> ('i, 'b) ibterm =
  fun m f t l ->
    match t, l with
    (* base cases *)
    | Y_Int_Arrow_Int, [a] ->
      let a = parse_int m a in
      H_Int (M_App (f, a))
    | Y_Bool_Arrow_Int, [a] ->
      let a = parse_bool m a in
      H_Int (M_App (f, term_of_formula a))
    | Y_Int_Arrow_Bool, [a] ->
      let a = parse_int m a in
      H_Bool (F_Atom (A_Bool (M_App (f, a))))
    | Y_Bool_Arrow_Bool, [a] ->
      let a = parse_bool m a in
      H_Bool (F_Atom (A_Bool (M_App (f, term_of_formula a))))
    (* erroneous base cases *)
    | Y_Int_Arrow_Int, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow_Int, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Int_Arrow_Bool, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow_Bool, _ ->
      raise (Smtlib_exn "wrong number of arguments")
    (* recursive cases *)
    | Y_Int_Arrow t, a :: l ->
      let a = parse_int m a in
      parse_app m (M_App (f, a)) t l
    | Y_Bool_Arrow t, a :: l ->
      let a = parse_bool m a in
      parse_app m (M_App (f, term_of_formula a)) t l
    (* erroneous recursive cases *)
    | Y_Int_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")
    | Y_Bool_Arrow _, [] ->
      raise (Smtlib_exn "wrong number of arguments")

and parse m = function
  | S_Atom k ->
    parse_nonlist m k
  | S_List [S_Atom L.K_Let; S_List l; e] ->
    parse_let m l e
  (* int cases *)
  | S_List (S_Atom L.K_Symbol "+" :: args) ->
    H_Int (sum args ~f:(parse_int m))
  (* bool cases *)
  | S_List (S_Atom L.K_Symbol "and" :: args) ->
    H_Bool (forall args ~f:(parse_bool m))
  | S_List (S_Atom L.K_Symbol "or" :: args) ->
    H_Bool (exists args ~f:(parse_bool m))
  | S_List (S_Atom L.K_Symbol "=>" :: args) ->
    (match List.rev args with
    | a :: d ->
      let init = parse_bool m a
      and f acc e = parse_bool m e => acc in
      H_Bool (List.fold_left d ~init ~f)
    | _ ->
      raise (Smtlib_exn "syntax error"))
  | S_List [S_Atom L.K_Symbol "not"; e] ->
    H_Bool (not (parse_bool m e))
  (* polymorphic cases *)
  | S_List [S_Atom L.K_Symbol "ite"; e1; e2; e3] ->
    let e1 = parse_bool m e1 in
    map_matching_types (parse m e2) (parse m e3)
      ~fi:(fun e2 e3 -> H_Int (M_Ite (e1, e2, e3)))
      ~fb:(fun e2 e3 -> H_Bool (F_Ite (e1, e2, e3)))
  | S_List [S_Atom L.K_Symbol "="; e1; e2] ->
    H_Bool (parse_eq m e1 e2)
  | S_List [S_Atom L.K_Symbol "distinct"; e1; e2] ->
    H_Bool (F_Not (parse_eq m e1 e2))
  | _ ->
    raise (Smtlib_exn "syntax error")
