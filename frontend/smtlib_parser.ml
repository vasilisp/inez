(* 

   A parser for SMT-LIB QF_UFLIA instances.

   This module translates formulas and terms to our GADT
   representation, but not commands (declare-fun, assert & co).

   Smtlib_solver parses commands and puts everything together, i.e.,
   calls the underlying solver in our usual functorial way.

*)

open Core.Std
open Logic
open Terminology

module F = Formula
module L = Smtlib_lexer

exception Smtlib_Exn of string

(* We first translate sequences of tokens to S-expressions. *)

type smtlib_sexp =
  S_List  of  smtlib_sexp list
| S_Atom  of  Smtlib_lexer.token'

type ctx = {
  r_ctx  :  Smtlib_lexer.ctx;
  r_buf  :  Lexing.lexbuf;
}

let make_ctx b = {
  r_ctx  =  L.make_ctx ();
  r_buf  =  b;
}

let get_line {r_ctx} = L.get_line r_ctx

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
    raise (Smtlib_Exn "unmatched parentheses")
  | L.T_Other k ->
    S_Atom k

(* We now translate smtlib_sexp to our GADT representation. *)

type 'c ibterm = (('c, int) M.t, 'c A.t F.t) ibeither

type 'c tbox = 'c Box.t

type 'c env = {
  e_find     :  string -> 'c tbox option;
  e_replace  :  string -> 'c tbox -> 'c env;
  e_type     :  't . ('c, 't) M.t -> 't Type.t
}

(* utilities *)

let tbx x = Type.Box.Box x

let lbx x = Box.Box x

let term_of_formula = function
  | F.F_Atom (A.A_Bool t) ->
    t
  | t ->
    M.M_Bool t

let sum ~f =
  (List.fold_left
     ~init:M.zero
     ~f:(fun acc x -> M.(acc + f x)))

let map_matching_types e1 e2 ~fi ~fb =
  Type.(match e1, e2 with
  | H_Int e1, H_Int e2 ->
    fi e1 e2
  | H_Bool e1, H_Bool e2 ->
    fb e1 e2
  | _ ->
    raise (Smtlib_Exn "type error"))

(* parsing functions *)

let rec parse_nonlist {e_find; e_type} = function
  | L.K_Int i ->
    H_Int (M.M_Int i)
  | L.K_Symbol "true" ->
    H_Bool F.F_True
  | L.K_Symbol "false" ->
    H_Bool (F.F_Not F.F_True)
  | L.K_Symbol s ->
    (match e_find s with
    | None ->
      raise (Smtlib_Exn "unknown id")
    | Some (Box.Box e) ->
      match e_type e with
      | Type.Y_Int ->
        H_Int e
      | Type.Y_Bool ->
        H_Bool (F.F_Atom (A.A_Bool e))
      | _ ->
        raise (Smtlib_Exn (Printf.sprintf "%s is a function" s)))
  | _ ->
    raise (Smtlib_Exn "syntax error")

let rec parse_let init l e =
  let m =
    List.fold_left l ~init
      ~f:(fun {e_replace; e_type} -> function
      | S_List [S_Atom (L.K_Symbol id); e] ->
        (match parse init e with
        | H_Int e ->
          e_replace id (lbx e)
        | H_Bool e ->
          e_replace id (lbx (term_of_formula e)))
      | _ ->
        raise (Smtlib_Exn "syntax error")) in
  parse m e

and parse_int m e =
  match parse m e with
  | H_Int i ->
    i
  | H_Bool _ ->
    raise (Smtlib_Exn "type error: int expected")

and parse_bool m e =
  match parse m e with
  | H_Bool b ->
    b
  | H_Int _ ->
    raise (Smtlib_Exn "type error: bool expected")

and parse_eq m e1 e2 =
  map_matching_types (parse m e1) (parse m e2)
    ~fi:(fun e1 e2 -> F.F_Atom (A.A_Eq M.(e1 - e2)))
    ~fb:(fun e1 e2 -> Ops.((e1 => e2) && (e2 => e1)))

and parse_mult m = function
  | [S_Atom (L.K_Int i); e] 
  | [e; S_Atom (L.K_Int i)] ->
    H_Int Ops.(i * parse_int m e)
  | [S_List [S_Atom L.K_Symbol "-"; S_Atom (L.K_Int i)]; e]
  | [e; S_List [S_Atom L.K_Symbol "-"; S_Atom (L.K_Int i)]] ->
    H_Int (Ops.( * ) (Int63.(~-) i) (parse_int m e))
  | _ ->
    raise (Smtlib_Exn "syntax error: non-linear term")

and parse_app_aux :
type t . 'c env -> ('c, t) M.t -> t Type.t ->
  smtlib_sexp list -> 'c ibterm =
  fun m f t l ->
    match t, l with
    (* base cases *)
    | Type.Y_Int, [] ->
      H_Int f
    | Type.Y_Bool, [] ->
      H_Bool (F.F_Atom (A.A_Bool f))
    (* erroneous base cases *)
    | Type.Y_Int, _ ->
      raise (Smtlib_Exn "wrong number of arguments")
    | Type.Y_Bool, _ ->
      raise (Smtlib_Exn "wrong number of arguments")
    (* recursive cases *)
    | Type.Y_Int_Arrow t, a :: l ->
      let a = parse_int m a in
      parse_app_aux m (M.M_App (f, a)) t l
    | Type.Y_Bool_Arrow t, a :: l ->
      let a = parse_bool m a in
      parse_app_aux m (M.M_App (f, term_of_formula a)) t l
    (* erroneous recursive cases *)
    | Type.Y_Int_Arrow _, [] ->
      raise (Smtlib_Exn "wrong number of arguments")
    | Type.Y_Bool_Arrow _, [] ->
      raise (Smtlib_Exn "wrong number of arguments")

and parse_app ({e_find; e_type} as m) s l =
  match e_find s with
  | None ->
    raise (Smtlib_Exn (Printf.sprintf "unknown id: %s" s))
  | Some (Box.Box e) ->
    (match e_type e with
    | Type.Y_Int ->
      raise (Smtlib_Exn "function expected")
    | Type.Y_Bool ->
      raise (Smtlib_Exn "function expected")
    | t ->
      parse_app_aux m e t l)

and parse m = function
  | S_Atom k ->
    parse_nonlist m k
  | S_List [S_Atom L.K_Let; S_List l; e] ->
    parse_let m l e
  (* int cases *)
  | S_List (S_Atom L.K_Symbol "+" :: args) ->
    H_Int (sum args ~f:(parse_int m))
  | S_List [S_Atom L.K_Symbol "-"; e] ->
    let e = parse_int m e in
    H_Int (M.(Int63.minus_one * e))
  | S_List (S_Atom L.K_Symbol "-" :: init :: args) ->
    let init = parse_int m init in
    H_Int
      (List.fold_left args
         ~f:(fun acc x -> M.(acc - parse_int m x)) ~init)
  | S_List (S_Atom L.K_Symbol "*" :: args) ->
    parse_mult m args
  (* bool cases *)
  | S_List (S_Atom L.K_Symbol "and" :: args) ->
    H_Bool (F.forall args ~f:(parse_bool m))
  | S_List (S_Atom L.K_Symbol "or" :: args) ->
    H_Bool (F.exists args ~f:(parse_bool m))
  | S_List (S_Atom L.K_Symbol "=>" :: args) ->
    (match List.rev args with
    | a :: d ->
      let init = parse_bool m a
      and f acc e = Ops.(parse_bool m e => acc) in
      H_Bool (List.fold_left d ~init ~f)
    | _ ->
      raise (Smtlib_Exn "syntax error"))
  | S_List [S_Atom L.K_Symbol "not"; e] ->
    H_Bool (F.not (parse_bool m e))
  (* bool-from-int cases *)
  | S_List [S_Atom L.K_Symbol "<"; e1; e2] ->
    let e1 = parse_int m e1
    and e2 = parse_int m e2 in
    H_Bool (Ops.(e1 < e2))
  | S_List [S_Atom L.K_Symbol "<="; e1; e2] ->
    let e1 = parse_int m e1
    and e2 = parse_int m e2 in
    H_Bool (Ops.(e1 <= e2))
  | S_List [S_Atom L.K_Symbol ">="; e1; e2] ->
    let e1 = parse_int m e1
    and e2 = parse_int m e2 in
    H_Bool (Ops.(e1 >= e2))
  | S_List [S_Atom L.K_Symbol ">"; e1; e2] ->
    let e1 = parse_int m e1
    and e2 = parse_int m e2 in
    H_Bool (Ops.(e1 > e2))
  (* polymorphic cases *)
  | S_List [S_Atom L.K_Symbol "ite"; e1; e2; e3] ->
    let e1 = parse_bool m e1 in
    map_matching_types (parse m e2) (parse m e3)
      ~fi:(fun e2 e3 -> H_Int (M.M_Ite (e1, e2, e3)))
      ~fb:(fun e2 e3 -> H_Bool (F.F_Ite (e1, e2, e3)))
  | S_List [S_Atom L.K_Symbol "="; e1; e2] ->
    H_Bool (parse_eq m e1 e2)
  | S_List [S_Atom L.K_Symbol "distinct"; e1; e2] ->
    H_Bool (F.F_Not (parse_eq m e1 e2))
  | S_List (S_Atom L.K_Symbol s :: l) ->
    parse_app m s l
  | _ ->
    raise (Smtlib_Exn "syntax error")
