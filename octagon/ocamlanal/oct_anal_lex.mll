(* oct_anal_lex.mll
   Lexer for the toy language for the example analyzer.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
*)

{
open Oct_anal_syn
open Oct_anal_yacc
} 

rule token = parse
    (* ignore spaces, tabs, and \r *)
      ['\r' ' ' '\t']+   { token lexbuf } 
    
    (* line count *)
    | '\n'
    { incr cur_line;
      line_offsets := ((Lexing.lexeme_end lexbuf), !cur_line):: !line_offsets;
      token lexbuf }

    (* comments: nested /* */, and // are allowed *)
    | "/*" { start_of_comment := Lexing.lexeme_start lexbuf;
             comment lexbuf ;
             token lexbuf }
    | "//"([^'\n']*)'\n' 
    { incr cur_line;
      line_offsets := ((Lexing.lexeme_end lexbuf), !cur_line):: !line_offsets;
      token lexbuf }
    | "//"([^'\n']*)     { token lexbuf }

    (* numbers *)
    | ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { T_NUM(float_of_string (Lexing.lexeme lexbuf)) }
    | '.' ['0'-'9']+ (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { T_NUM(float_of_string (Lexing.lexeme lexbuf)) }

    (* keywords *)
    | "program"      { T_PROG }
    | "beginprogram" { T_BEGINPROG ((Lexing.lexeme_start lexbuf)+12) }
    | "endprogram"   { T_ENDPROG ((Lexing.lexeme_start lexbuf)-1) }
    | "true"   { T_TRUE }
    | "false"  { T_FALSE }
    | "assert" { T_ASSERT }
    | "while"  { T_WHILE }
    | "do"     { T_DO ((Lexing.lexeme_start lexbuf)+2) }
    | "done"   { T_DONE ((Lexing.lexeme_start lexbuf)-1) }
    | "if"     { T_IF }
    | "then"   { T_THEN ((Lexing.lexeme_start lexbuf)+4) }
    | "else"   { T_ELSE ((Lexing.lexeme_start lexbuf)-1) }
    | "begin"  { T_BEGIN ((Lexing.lexeme_start lexbuf)+5) }
    | "end"    { T_END ((Lexing.lexeme_start lexbuf)-1) }
    | ";"      { T_SEMICOLON ((Lexing.lexeme_start lexbuf)+1) }
    | "("      { T_LPAR }
    | ")"      { T_RPAR }
    | "<="     { T_LEQ }
    | ">="     { T_GEQ }
    | "<"      { T_L }
    | ">"      { T_G }
    | "!="     { T_NEQ }
    | "="      { T_EQ }
    | "*"      { T_TIMES }
    | "+"      { T_PLUS }
    | "-"      { T_MINUS }
    | "not"    { T_NOT }
    | "and"    { T_AND }
    | "or"     { T_OR }
    | "brandom" { T_BRAND }
    | "random"  { T_RAND }

    (* identifiers *)
    | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
                  { T_ID (Lexing.lexeme lexbuf) }

    (* end of file *)
    | eof         { T_EOF }
    | '\004'      { T_EOF }


    (* handles nested /* */ comments *)

and comment = parse
    "/*"   { comment lexbuf; comment lexbuf }
  | "*/"   { () }
  | '\n' { incr cur_line;
           line_offsets :=
             ((Lexing.lexeme_end lexbuf), !cur_line):: !line_offsets;
           comment lexbuf }
  | [^'\n' '*' '/']+ { comment lexbuf }
  | _              { comment lexbuf }
  | eof            { raise (Unterminated_comment !start_of_comment) }

