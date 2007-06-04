
{
  open Lexing 
  open Mix_parser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ (* logic *)
	"and", AND;
        "exists", EXISTS;
	"false", FALSE;
	"forall", FORALL;
	"not", NOT;
	"or", OR;
	"true", TRUE;
	(* asm *)
	"jump", JUMP;
	"jcond", JCOND;
	"halt", HALT;
      ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  exception Lexical_error of string
}

let newline = '\n'
let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z']
let letter = alpha | '_'
let digit = ['0'-'9']
let ident = letter (letter | digit | '\'')*

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | ident as id  
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | ident as id ":"
      { LABEL id }
  | "{{"
      { LBRALBRA }
  | "}}" 
      { RBRARBRA }
  | "(*"
      { comment lexbuf; token lexbuf }
  | "\""
      { Buffer.clear string_buf; string lexbuf }
  | eof 
      { EOF }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }

and comment = parse
  | "*)" 
      { () }
  | "(*" 
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
