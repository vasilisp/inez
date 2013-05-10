exception Smtlib_Exn of string

type smtlib_sexp =
  S_List of smtlib_sexp list | S_Atom of Smtlib_lexer.token'

type ctx

val make_ctx : Lexing.lexbuf -> ctx

val get_line : ctx -> int

val get_smtlib_sexp : ?token:Smtlib_lexer.token -> ctx -> smtlib_sexp

type 'c ibterm =
  (('c, int) Lang_abstract.M.t,
   'c Lang_abstract.A.t Formula.t) Terminology.ibeither

type 'c env = {
  e_find : string -> 'c Lang_abstract.Box.t option;
  e_replace : string -> 'c Lang_abstract.Box.t -> 'c env;
  e_type : 't. ('c, 't) Lang_abstract.M.t -> 't Lang_types.t;
}

val parse : 'c env -> smtlib_sexp -> 'c ibterm
