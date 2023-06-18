{
  open Lexing
  open Parser

  exception SyntaxError of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      {
        pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1
      }
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

let id = ['a'-'z' 'A'-'Z' '_']+

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?
let int = '-'? ['0'-'9'] ['0'-'9']*

rule read =
  parse
  | white { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "true" { TRUE }
  | "false" { FALSE }
  | "(" { LPARENS }
  | ")" { RPARENS }
  | "let" { LET }
  | "in" { IN }
  | "=" { EQUALS }
  | ":" { COLON }
  | "->" { ARROW }
  | "fun" { FUN }
  (* TODO: remove "int" and "bool", and stay only with type identifiers *)
  | "int" { TINT }
  | "bool" { TBOOL }
  | id { IDENT (Lexing.lexeme lexbuf) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof { EOF }