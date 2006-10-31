
(* $Id: jc_lexer.mli,v 1.2 2006-10-31 08:25:16 marche Exp $ *)

exception Lexical_error of Loc.position * string

exception Syntax_error of Loc.position

val token : Lexing.lexbuf -> Jc_parser.token

val parse  : string -> in_channel -> Jc_ast.decl list


