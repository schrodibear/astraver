
(* $Id: jc_lexer.mli,v 1.1 2006-10-30 16:47:50 marche Exp $ *)

exception Lexical_error of string

val token : Lexing.lexbuf -> Parser.token

val parse_file  : Lexing.lexbuf -> Ptree.file
val parse_lexpr : Lexing.lexbuf -> Ptree.lexpr

val lexpr_of_string : string -> Ptree.lexpr

