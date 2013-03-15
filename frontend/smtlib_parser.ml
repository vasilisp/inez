open Core.Std

module L = Smtlib_lexer

type smtlib_sexp =
  S_List of smtlib_sexp list
| S_Atom of Smtlib_lexer.token

let rec parse_list ~f ~acc () =
  match f () with
  | L.T_RParen ->
    List.rev acc
  | token ->
    let acc = parse ~token ~f () :: acc in
    parse_list ~f ~acc ()

and parse ?token ~f () =
  let token = match token with Some token -> token | None -> f () in
  match token with
  | L.T_LParen ->
    S_List (parse_list ~f ~acc:[] ())
  | token ->
    S_Atom token
    
