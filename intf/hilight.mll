{
  type token = Code of string | Annotation of string
  exception Lex_error of string
}

rule next_code = parse
  | [^'{']* { let c = (Code(Lexing.lexeme lexbuf)) in c::(next_code lexbuf) }
  | '{'  { let a = Annotation("{"^(next_annotation lexbuf)) in a ::(next_code lexbuf)}
   | eof  { [] }
and next_annotation = parse
  | [^'}']*'}' {Lexing.lexeme lexbuf}
  | _ { raise (Lex_error "Error in annotation")}
  | eof  { raise (Lex_error "No closing }") }

and next_code_c = parse
  | "/*"  
      { let a = Annotation ("/*" ^ next_annotation_c lexbuf) in 
	a :: next_code_c lexbuf }
  | [^'/']*
      { let c = Code (Lexing.lexeme lexbuf) in c :: (next_code_c lexbuf) }
  | eof  
      { [] }
and next_annotation_c = parse
  | [^'/']* "*/"
      { Lexing.lexeme lexbuf }
  | _ { raise (Lex_error "Error in annotation") }
  | eof  
      { raise (Lex_error "No closing }") }

