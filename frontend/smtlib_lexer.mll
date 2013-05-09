{
 
  open Core.Std

  type ctx = {
    mutable c_n_lines: int
  }

  let make_ctx () = {
    c_n_lines = 0
  }
    
  type token' =
    K_Int of Int63.t
  | K_Decimal of float
  | K_String of string
  | K_Symbol of string
  | K_Quoted of string
  | K_Key of string
  | K_Let
  | K_Par
  | K_Underscore
  | K_Bang
  | K_As
  | K_Forall
  | K_Exists
  | K_Set_Logic
  | K_Set_Option
  | K_Set_Info
  | K_Declare_Sort
  | K_Define_Sort
  | K_Declare_Fun
  | K_Define_Fun
  | K_Push (* *)
  | K_Pop (* *)
  | K_Assert (* *)
  | K_Check_Sat (* *)
  | K_Get_Assertions (* *)
  | K_Get_Proof (* *)
  | K_Get_Unsat_Core (* *)
  | K_Get_Value
  | K_Get_Assignment
  | K_Get_Option (* *)
  | K_Get_Info (* *)
  | K_Exit

  type token =
    T_LParen
  | T_RParen
  | T_Other of token'

  let string_of_token' = function
    | K_Int i -> Int63.to_string i
    | K_Decimal d -> Float.to_string d
    | K_String s -> s
    | K_Symbol s -> s
    | K_Quoted q -> "blah"
    | K_Key key -> ":" ^ key
    | K_Let -> "let"
    | K_Par -> "par"
    | K_Underscore -> "_"
    | K_Bang -> "!"
    | K_As -> "as"
    | K_Forall -> "forall"
    | K_Exists -> "exists"
    | K_Set_Logic -> "set-logic"
    | K_Set_Option -> "set-option"
    | K_Set_Info -> "set-info"
    | K_Declare_Sort -> "declare-sort"
    | K_Define_Sort -> "define-sort"
    | K_Declare_Fun -> "declare-fun"
    | K_Define_Fun -> "define-fun"
    | K_Push -> "push"
    | K_Pop -> "pop"
    | K_Assert -> "assert"
    | K_Check_Sat -> "check-sat"
    | K_Get_Assertions -> "get-assertions"
    | K_Get_Proof -> "get-proof"
    | K_Get_Unsat_Core -> "get-unsat-core"
    | K_Get_Value -> "get-value"
    | K_Get_Assignment -> "get-assignment"
    | K_Get_Option -> "get-option"
    | K_Get_Info -> "get-info"
    | K_Exit -> "exit"

  let string_of_token = function
    | T_LParen -> "("
    | T_RParen -> ")"
    | T_Other k -> string_of_token' k

  let get_line {c_n_lines} = c_n_lines

}

let whitespace =
  [ ' ' '\t' ]

let comment = ';' [^ '\n']* 

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
  | "let"              { T_Other K_Let }
  | "par"              { T_Other K_Par }
  | "_"                { T_Other K_Underscore }
  | "!"                { T_Other K_Bang }
  | "as"               { T_Other K_As }
  | "let"              { T_Other K_Let }
  | "forall"           { T_Other K_Forall }
  | "exists"           { T_Other K_Exists }
  | "set-logic"        { T_Other K_Set_Logic }
  | "set-option"       { T_Other K_Set_Option }
  | "set-info"         { T_Other K_Set_Info }
  | "declare-sort"     { T_Other K_Declare_Sort }
  | "define-sort"      { T_Other K_Define_Sort }
  | "declare-fun"      { T_Other K_Declare_Fun }
  | "define-fun"       { T_Other K_Define_Fun }
  | "push"             { T_Other K_Push }
  | "pop"              { T_Other K_Pop }
  | "assert"           { T_Other K_Assert }
  | "check-sat"        { T_Other K_Check_Sat }
  | "get-assertions"   { T_Other K_Get_Assertions }
  | "get-proof"        { T_Other K_Get_Proof }
  | "get-unsat-core"   { T_Other K_Get_Unsat_Core }
  | "get-value"        { T_Other K_Get_Value }
  | "get-assignment"   { T_Other K_Get_Assignment }
  | "get-option"       { T_Other K_Get_Option }
  | "get-info"         { T_Other K_Get_Info }
  | "exit"             { T_Other K_Exit }
  (* numbers *)
  | numeral as n       { T_Other (K_Int (Int63.of_string n)) }
  | binary as b        { let s = String.copy b in
                         String.set s 0 '0';
                         T_Other (K_Int (Int63.of_string s)) }
  | hex as h           { let s = String.copy h in
                         String.set h 0 '0';
                         T_Other (K_Int (Int63.of_string s)) }
  | decimal as d       { T_Other (K_Decimal (Float.of_string d)) }
  (* symbols and keywords*)
  | simple_symbol as s { T_Other (K_Symbol s) }
  | keyword as kwd     { let len = String.length kwd - 1 in
                         T_Other (K_Key (String.sub kwd ~pos:1 ~len)) }
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
    | '"'              { T_Other (K_String "FIXME") }

and quoted_token ctx = parse
    | [^ '\n' '|']     { quoted_token ctx lexbuf }
    | '\n'             { ctx.c_n_lines <- ctx.c_n_lines + 1;
                         quoted_token ctx lexbuf }
    | '|'              { T_Other (K_Quoted "FIXME") }

{}
