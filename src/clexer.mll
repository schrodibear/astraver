
(* from http://www.lysator.liu.se/c/ANSI-C-grammar-l.html *)

{

  open Cparser
  open Lexing

  let loc lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)

  let lex_error lexbuf s =
    raise (Stdpp.Exc_located (loc lexbuf, Stream.Error s))

}

let rD =	['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rFS	= ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | [' ' '\t' '\n']+        { token lexbuf }
  | "/*"                    { comment lexbuf; token lexbuf }

  | "auto"                  { AUTO }
  | "break"                 { BREAK }
  | "case"                  { CASE }
  | "char"                  { CHAR }
  | "const"                 { CONST }
  | "continue"              { CONTINUE }
  | "default"               { DEFAULT }
  | "do"                    { DO }
  | "double"                { DOUBLE }
  | "else"                  { ELSE }
  | "enum"                  { ENUM }
  | "extern"                { EXTERN }
  | "float"                 { FLOAT }
  | "for"                   { FOR }
  | "goto"                  { GOTO }
  | "if"                    { IF }
  | "int"                   { INT }
  | "long"                  { LONG }
  | "register"              { REGISTER }
  | "return"                { RETURN }
  | "short"                 { SHORT }
  | "signed"                { SIGNED }
  | "sizeof"                { SIZEOF }
  | "static"                { STATIC }
  | "struct"                { STRUCT }
  | "switch"                { SWITCH }
  | "typedef"               { TYPEDEF }
  | "union"                 { UNION }
  | "unsigned"              { UNSIGNED }
  | "void"                  { VOID }
  | "volatile"              { VOLATILE }
  | "while"                 { WHILE }

  | rL (rL | rD)*           { IDENTIFIER (lexeme lexbuf) }

  | '0'['x''X'] rH+ rIS?    { CONSTANT (lexeme lexbuf)}
  | '0' rD+ rIS?            { CONSTANT (lexeme lexbuf) }
  | rD+ rIS?                { CONSTANT (lexeme lexbuf) }
  | 'L'? "'" (_|[^'\\''\''])+ "'"     { CONSTANT (lexeme lexbuf) }

  | rD+ rE rFS?             { CONSTANT (lexeme lexbuf) }
  | rD* "." rD+ (rE)? rFS?  { CONSTANT (lexeme lexbuf) }
  | rD+ "." rD* (rE)? rFS?  { CONSTANT (lexeme lexbuf) }

  | 'L'? '"' (_|[^'\\''"'])* '"'     { STRING_LITERAL (lexeme lexbuf) }

  | "..."                   { ELLIPSIS }
  | ">>="                   { RIGHT_ASSIGN }
  | "<<="                   { LEFT_ASSIGN }
  | "+="                    { ADD_ASSIGN }
  | "-="                    { SUB_ASSIGN }
  | "*="                    { MUL_ASSIGN }
  | "/="                    { DIV_ASSIGN }
  | "%="                    { MOD_ASSIGN }
  | "&="                    { AND_ASSIGN }
  | "^="                    { XOR_ASSIGN }
  | "|="                    { OR_ASSIGN }
  | ">>"                    { RIGHT_OP }
  | "<<"                    { LEFT_OP }
  | "++"                    { INC_OP }
  | "--"                    { DEC_OP }
  | "->"                    { PTR_OP }
  | "&&"                    { AND_OP }
  | "||"                    { OR_OP }
  | "<="                    { LE_OP }
  | ">="                    { GE_OP }
  | "=="                    { EQ_OP }
  | "!="                    { NE_OP }
  | ";"                     { SEMICOLON }
  | ("{"|"<%")              { LBRACE }
  | ("}"|"%>")              { RBRACE }
  | ","                     { COMMA }
  | ":"                     { COLON }
  | "="                     { EQUAL }
  | "("                     { LPAR }
  | ")"                     { RPAR }
  | ("["|"<:")              { RSQUARE }
  | ("]"|":>")              { RSQUARE }
  | "."                     { DOT }
  | "&"                     { AMP }
  | "!"                     { EXL }
  | "~"                     { TILDE }
  | "-"                     { MINUS }
  | "+"                     { PLUS }
  | "*"                     { STAR }
  | "/"                     { SLASH }
  | "%"                     { PERCENT }
  | "<"                     { LT }
  | ">"                     { GT }
  | "^"                     { HAT }
  | "|"                     { PIPE }
  | "?"                     { QUESTION }

  | eof { EOF }
  | _   { lex_error lexbuf ("Illegal_character " ^ lexeme lexbuf) }

and comment = parse
  | "*/" { () }
  | _    { comment lexbuf }
  | eof  { lex_error lexbuf "Unterminated_comment" }

{

}
