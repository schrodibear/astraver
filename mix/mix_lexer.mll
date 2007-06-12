
{
  open Lexing 
  open Mix_ast
  open Mix_parser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "jmp", INSTR Jmp;
	"jge", INSTR Jge;
	"j3p", INSTR J3p;
	(* loading *)
	"lda", INSTR Lda;
	(* address transfer *)
	"ent1", INSTR Ent1;
	"ent2", INSTR Ent2;
	"ent3", INSTR Ent3;
	"ent4", INSTR Ent4;
	"ent5", INSTR Ent5;
	"ent6", INSTR Ent6;
	"dec1", INSTR Dec1;
	"dec2", INSTR Dec2;
	"dec3", INSTR Dec3;
	"dec4", INSTR Dec4;
	"dec5", INSTR Dec5;
	"dec6", INSTR Dec6;
        (* comparison *)
        "cmpa", INSTR Cmpa;
	(* other *)
	"halt", INSTR Halt;
	(* pseudo *)
	"equ", EQU;
	"orig", ORIG;
      ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

  exception Lexical_error of string
}

let newline = '\n'
let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z']
let letter = alpha | '_'
let digit = ['0'-'9']
let ident = letter (letter | digit | '\'')*
let integer = digit+

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | ident as id  
      { let lid = String.lowercase id in
	try Hashtbl.find keywords lid with Not_found -> IDENT id }
  | ident as id ":"
      { LABEL id }
  | integer as n
      { INTEGER n }
  | "{{{"
      { Buffer.clear string_buf; verbatim lexbuf }
  | "{{"
      { Buffer.clear string_buf; invariant lexbuf }
  | "{"
      { Buffer.clear string_buf; assertion lexbuf }
  | "/*"
      { comment lexbuf; token lexbuf }
  | "\""      { Buffer.clear string_buf; string lexbuf }
  | ","
      { COMMA }
  | ":"
      { COLON }
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { STAR }
  | eof 
      { EOF }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }

and comment = parse
  | "*/" 
      { () }
  | "/*" 
      { comment lexbuf; comment lexbuf }
  | newline 
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Lexical_error "unterminated comment") }
  | _ 
      { comment lexbuf }

and string = parse
  | "\""
      { STRING (Buffer.contents string_buf) }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline 
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Lexical_error "unterminated string") }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }

and verbatim = parse
  | "}}}" 
      { VERBATIM (Buffer.contents string_buf) }
  | eof
      { raise (Lexical_error "unterminated verbatim") }
  | _ as c
      { Buffer.add_char string_buf c; verbatim lexbuf }

and invariant = parse
  | "}}" 
      { INVARIANT (Buffer.contents string_buf) }
  | eof
      { raise (Lexical_error "unterminated invariant") }
  | _ as c
      { Buffer.add_char string_buf c; invariant lexbuf }

and assertion = parse
  | "}" 
      { ASSERT (Buffer.contents string_buf) }
  | eof
      { raise (Lexical_error "unterminated assert") }
  | _ as c
      { Buffer.add_char string_buf c; assertion lexbuf }
