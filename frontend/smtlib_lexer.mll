{
 
  open Core.Std

  type ctx = 
    { mutable c_n_lines: int }

  let make_ctx () = { c_n_lines = 0}

  type token =
    T_LParen
  | T_RParen
  | T_Int of int
  | T_Decimal of float
  | T_String of string
  | T_Symbol of string
  | T_Quoted of string
  | T_Key of string
  | T_Let
  | T_Par
  | T_Underscore
  | T_Bang
  | T_As
  | T_Forall
  | T_Exists
  | T_Set_Logic
  | T_Set_Option
  | T_Set_Info
  | T_Declare_Sort
  | T_Define_Sort
  | T_Declare_Fun
  | T_Define_Fun
  | T_Push
  | T_Pop
  | T_Assert
  | T_Check_Sat
  | T_Get_Assertions
  | T_Get_Proof
  | T_Get_Unsat_Core
  | T_Get_Value
  | T_Get_Assignment
  | T_Get_Option
  | T_Get_Info
  | T_Exit

  let string_of_token = function
    | T_LParen -> "("
    | T_RParen -> ")"
    | T_Int i -> string_of_int i
    | T_Decimal d -> Float.to_string d
    | T_String s -> s
    | T_Symbol s -> s
    | T_Quoted q -> "blah"
    | T_Key key -> ":" ^ key
    | T_Let -> "let"
    | T_Par -> "par"
    | T_Underscore -> "_"
    | T_Bang -> "!"
    | T_As -> "as"
    | T_Forall -> "forall"
    | T_Exists -> "exists"
    | T_Set_Logic -> "set-logic"
    | T_Set_Option -> "set-option"
    | T_Set_Info -> "set-info"
    | T_Declare_Sort -> "declare-sort"
    | T_Define_Sort -> "define-sort"
    | T_Declare_Fun -> "declare-fun"
    | T_Define_Fun -> "define-fun"
    | T_Push -> "push"
    | T_Pop -> "pop"
    | T_Assert -> "assert"
    | T_Check_Sat -> "check-sat"
    | T_Get_Assertions -> "get-assertions"
    | T_Get_Proof -> "get-proof"
    | T_Get_Unsat_Core -> "get-unsat-core"
    | T_Get_Value -> "get-value"
    | T_Get_Assignment -> "get-assignment"
    | T_Get_Option -> "get-option"
    | T_Get_Info -> "get-info"
    | T_Exit -> "exit"

}

let whitespace =
  [ ' ' '\t' ]

let comment = ';' [^ '\n' ]

let numeral = '0' | (['1' - '9'] ['0' - '9']*)

let decimal = (('0' | (['1' - '9'] ['0' - '9']*)) '.' ['0' - '9']+)

let binary = ("#b" ['0' - '1']+)

let hex = ("#x" ['0' - '9' 'a' - 'f' 'A' - 'F' ]+)

let letter_etc =
  [ 'A' - 'Z' 'a' - 'z'
      '~' '!' '@' '$' '%' '^' '*' '_'
      '+' '=' '<' '>' '.' '?' '/' '-' ]

let letter_num_etc = 
  [ 'A' - 'Z' 'a' - 'z' '0' - '9'
      '~' '!' '@' '$' '%' '^' '*' '_'
      '+' '=' '<' '>' '.' '?' '/' '-' ]

let simple_symbol = (letter_etc letter_num_etc*)

let keyword = (':' letter_num_etc+)

rule token ctx = parse
  | whitespace         { token ctx lexbuf }
  | comment            { token ctx lexbuf }
  | "("                { T_LParen }
  | ")"                { T_RParen }
  (* reserved *)
  | "let"              { T_Let }
  | "par"              { T_Par }
  | "_"                { T_Underscore }
  | "!"                { T_Bang }
  | "as"               { T_As }
  | "let"              { T_Let }
  | "forall"           { T_Forall }
  | "exists"           { T_Exists }
  | "set-logic"        { T_Set_Logic }
  | "set-option"       { T_Set_Option }
  | "set-info"         { T_Set_Info }
  | "declare-sort"     { T_Declare_Sort }
  | "define-sort"      { T_Define_Sort }
  | "declare-fun"      { T_Declare_Fun }
  | "define-fun"       { T_Define_Fun }
  | "push"             { T_Push }
  | "pop"              { T_Pop }
  | "assert"           { T_Assert }
  | "check-sat "       { T_Check_Sat }
  | "get-assertions"   { T_Get_Assertions }
  | "get-proof"        { T_Get_Proof }
  | "get-unsat-core"   { T_Get_Unsat_Core }
  | "get-value"        { T_Get_Value }
  | "get-assignment"   { T_Get_Assignment }
  | "get-option"       { T_Get_Option }
  | "get-info"         { T_Get_Info }
  | "exit"             { T_Exit }
  (* numbers *)
  | numeral as n       { T_Int (int_of_string n) }
  | binary as b        { let s = String.copy b in
                         String.set s 0 '0';
                         T_Int (int_of_string s) }
  | hex as h           { let s = String.copy h in
                         String.set h 0 '0';
                         T_Int (int_of_string s) }
  | decimal as d       { T_Decimal (Float.of_string d) }
  (* symbols and keywords*)
  | simple_symbol as s { T_Symbol s }
  | keyword as kwd     { let len = String.length kwd - 1 in
                         T_Key (String.sub kwd ~pos:1 ~len) }
  (* modes and counting *)
  | "\""               { string_token ctx lexbuf }
  | '|'                { quoted_token ctx lexbuf }
  | eof                { raise End_of_file }
  | '\n'               { ctx.c_n_lines <- ctx.c_n_lines + 1;
                         token ctx lexbuf }
  | _                  { failwith
                           ((Lexing.lexeme lexbuf) ^
                               ": lexing error on line " ^
                               string_of_int ctx.c_n_lines) }

and string_token ctx = parse
    | "\\\""           { string_token ctx lexbuf }
    | [^ '\n' '"']     { string_token ctx lexbuf }
    | '\n'             { ctx.c_n_lines <- ctx.c_n_lines + 1;
                         string_token ctx lexbuf }
    | '"'              { token ctx lexbuf }

and quoted_token ctx = parse
    | [^ '\n' '|']     { quoted_token ctx lexbuf }
    | '\n'             { ctx.c_n_lines <- ctx.c_n_lines + 1;
                         quoted_token ctx lexbuf }
    | '|'              { token ctx lexbuf }

{

  let main () =
    let cin =
      if Array.length Sys.argv > 1 then
        open_in Sys.argv.(1)
      else
        stdin in
    let lexbuf = Lexing.from_channel cin in
    let ctx = make_ctx () in
    let rec do_stuff () =
      print_endline (string_of_token (token ctx lexbuf));
      do_stuff () in
    do_stuff ()

  let _ = main ()

}
