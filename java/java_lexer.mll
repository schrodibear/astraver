(***************************************************************************

Lexer for JavaCard source files

VerifiCard Project - Démons research team - LRI - Université Paris XI

$Id: java_lexer.mll,v 1.1 2007-03-06 10:44:18 marche Exp $

***************************************************************************)


{

  open Java_parser
  open Lexing
  open Java_ast

  type location = position * position

  let loc lexbuf : location = 
    (lexeme_start_p lexbuf, lexeme_end_p lexbuf)

  exception Lexical_error of location * string
  exception Syntax_error of location
  exception Dotdot of string


  let lex_error lexbuf s = raise (Lexical_error(loc lexbuf,s))

  let buf = Buffer.create 97

  let kw_table = 
    let table = Hashtbl.create 17 in
    let _ = 
      List.iter
	(fun (s,t) -> Hashtbl.add table s t)
	[ "abstract", ABSTRACT;
	  "axiom", AXIOM;
	  "behavior", BEHAVIOR;
	  "boolean", BOOLEAN;
	  "break", BREAK;
	  "byte", BYTE;
	  "byvalue", BYVALUE;
	  "case", CASE;
	  "cast", CAST;
	  "catch", CATCH;
	  "char", CHAR;
	  "class", CLASS;
	  "const", CONST;
	  "continue", CONTINUE;
	  "default", DEFAULT;
	  "do", DO;
	  "double", DOUBLE;
	  "else", ELSE;
	  "ensures", ENSURES;
	  "extends", EXTENDS;
	  "false", FALSE;
	  "final", FINAL;
	  "finally", FINALLY;
	  "float", FLOAT;
	  "for", FOR;
	  "future", FUTURE;
	  "generic", GENERIC;
	  "goto", GOTO;
	  "if", IF;
	  "implements", IMPLEMENTS;
	  "import", IMPORT;
	  "inner", INNER;
	  "instanceof", INSTANCEOF;
	  "int", INT;
	  "interface", INTERFACE;
	  "long", LONG;
	  "native", NATIVE;
	  "new", NEW;
	  "null", NULL;
	  "operator", OPERATOR;
	  "outer", OUTER;
	  "package", PACKAGE;
	  "private", PRIVATE;
	  "protected", PROTECTED;
	  "public", PUBLIC;
	  "requires", REQUIRES;
	  "rest", REST;
	  "return", RETURN;
	  "short", SHORT;
	  "static", STATIC;
	  "super", SUPER;
	  "switch", SWITCH;
	  "synchronized", SYNCHRONIZED;
	  "this", THIS;
	  (* "threadsafe" ? *)
	  "throw", THROW;
	  "throws", THROWS;
	  "transient", TRANSIENT;
	  "true", TRUE;
	  "try", TRY;
	  "var", VAR;
	  "void", VOID;
	  "volatile", VOLATILE;
	  "while", WHILE;	
	]
    in table

  let id_or_kw s =
    try
      let k = Hashtbl.find kw_table s in
      (*i
	prerr_string "Keyword ";
	prerr_endline s;
	i*)
      k
    with
	Not_found ->
	  (*i
	    prerr_string "Ident ";
	    prerr_endline s;
	    i*)
	  (ID s)

  let special_kw_table = 
    let table = Hashtbl.create 17 in
    let _ = 
      List.iter
	(fun (s,t) -> Hashtbl.add table s t)
	[ (* "everything", BSEVERYTHING ; *)
	  "exists", BSEXISTS ;
	  (* "fresh", BSFRESH ; *)
	  "forall", BSFORALL ;
	  (* "nothing", BSNOTHING;
	  "fields_of", BSFIELDSOF;
          "not_conditionally_updated", BSNOTCONDITIONALLYUPDATED;
	  *)
	  "old", BSOLD;
	  "result", BSRESULT;
	  (*"type", BSTYPE;
	  "typeof", BSTYPEOF;
	  "fpi", BSFPI; *)
	]
    in table

  let special_id lexbuf s =
    try
      Hashtbl.find special_kw_table s
    with
	Not_found ->
	  lex_error lexbuf ("unknown special JML keyword \\"^s)

(*

  let jml_spec_token base jml_string =
(*i
    Format.fprintf Config.log "In file %s, parsing JML Spec: %s@."
      (Location.base_filename base) jml_string;
i*)
    match Jml_syntax.parse_jml_specification base jml_string with 
    | Ast_types.Jml_declaration d -> JML_DECLARATIONS(d)
    | Ast_types.Jml_method_specification s -> JML_METHOD_SPECIFICATION(s)
    | Ast_types.Jml_loop_annotation la -> JML_LOOP_ANNOTATION(la)
    | Ast_types.Jml_assertion a -> JML_ASSERTION(a)
    | Ast_types.Jml_annotation_statement Ast_types.Set_statement s -> JML_ANNOTATION_STATEMENT(Ast_types.Set_statement(s))
    | Ast_types.Jml_axiom(id,e) -> JML_AXIOM(id,e)
    | Ast_types.Jml_type(id) -> JML_TYPE(id)
    | Ast_types.Jml_logic_reads(id,t,p,r) -> JML_LOGIC_READS(id,t,p,r)
    | Ast_types.Jml_logic_def(id,t,p,e) -> JML_LOGIC_DEF(id,t,p,e)
    assert false

*)
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; 
	  pos_bol = pos.pos_cnum }

}

let space = [' ' '\t' '\r']
let backslash_escapes =
  ['\\' '"' '\'' 'n' 't' 'b' 'r' 'f' (* octal manque ! *)]

rule token = parse
  | space+
      { token lexbuf }
  | '\n' 
      { newline lexbuf; token lexbuf }
  | "/*@"               
      { let loc = lexeme_start_p lexbuf in
	Buffer.clear buf; ANNOT(loc,annot lexbuf) }
  | "//@" ([^ '\n']* as a) '\n'  
      { let loc = lexeme_start_p lexbuf in
	newline lexbuf;	ANNOT(loc,a) }
  | "/*"
      { comment lexbuf; token lexbuf }
  | "//" ([^'\n''@'][^'\n']*)? '\n'
      { newline lexbuf; token lexbuf }
  | "\\" (['A'-'Z''a'-'z''_']['A'-'Z''a'-'z''0'-'9''_']* as id)
      { special_id lexbuf id }
  | ['A'-'Z''a'-'z''_']['A'-'Z''a'-'z''0'-'9''_']* as id
      { id_or_kw id }
  | ';'
      { SEMICOLON }
  | ','
      { COMMA }
  | '.'
      { DOT }
  | '+'                 
      { PLUS }
  | '-'       
      { MINUS }
  | "++"                 
      { PLUSPLUS }
  | "--"       
      { MINUSMINUS }
  | '*'
      { STAR }
  | '/'
      { SLASH }
  | '%'
      { PERCENT }
  | "&"
      { AMPERSAND }
  | "|"
      { VERTICALBAR }
  | "&&"
      { AMPERSANDAMPERSAND }
  | "||"
      { VERTICALBARVERTICALBAR }
  | "=>"
      { EQGT }
  | "!"
      { BANG }
  | "~"
      { TILDA }
  | "^"
      { CARET }
  | "?"
      { QUESTIONMARK }
  | ":"
      { COLON }
  | "<<" 
      { SHIFT Blsl }
  | ">>" 
      { SHIFT Blsr }
  | ">>>"
      { SHIFT Basr }
  | "=" 
      { EQ }
  | ("*=" | "/=" | "%=" | "+=" | "-=" 
    | "<<=" | ">>=" | ">>>=" | "&=" | "^=" | "|=") as op
      { ASSIGNOP(op) }
  | ">" 
      { COMP Bgt }
  | "<" 
      { COMP Blt }
  | "<=" 
      { COMP Ble }
  | ">="
      { COMP Bge }
  | "==" 
      { EQOP Beq }
  | "!="
      { EQOP Bne }

      (* decimal constants *)

  | ('0' | ['1'-'9']['0'-'9']*) ['l''L']? as n
      { INTEGER n }

      (* octal constants *)

  | '0'['0'-'7']+ ['l''L']? as n         
      { INTEGER ("0o" ^ n) }

      (* hexadecimal constants *)

  | '0'['x''X']['0'-'9' 'A'-'F' 'a'-'f']+['l''L']? as n 
    { INTEGER n }

      (* floating-point constants *)

  | ['0'-'9']+ '.' ['0'-'9']* (['e''E']['-''+']?['0'-'9']+)? ['f''F''d''D'] ?
      { REAL (lexeme lexbuf) }

  | '.' ['0'-'9']+ (['e''E']['-''+']?['0'-'9']+)? ['f''F''d''D'] ?
      { REAL (lexeme lexbuf) }

  | ['0'-'9']+ ['e''E'] ['-''+']?['0'-'9']+ ['f''F''d''D'] ?
      { REAL (lexeme lexbuf) }

      (* character constants *)

  | "'" _ "'" as s
      { CHARACTER s }

  | "'\\" backslash_escapes "'" as s
      { CHARACTER s }

  | "'\\u" ['0'-'9''A'-'F'] ['0'-'9''A'-'F'] 
      ['0'-'9''A'-'F'] ['0'-'9''A'-'F'] "'" as s
      { CHARACTER s }

  | '('
      { LEFTPAR }
  | ')'
      { RIGHTPAR }
  | '{'
      { LEFTBRACE }
  | '}'
      { RIGHTBRACE }
  | '['
      { LEFTBRACKET }
  | ']'
      { RIGHTBRACKET }
  | '"'
      { Buffer.clear buf; STRING(string lexbuf) }
  | _ 
      { lex_error lexbuf ("unexpected char `" ^ lexeme lexbuf ^ "'") }
  | eof
      { EOF }

and string = parse
  | '"'
      { Buffer.contents buf }
  | '\\' backslash_escapes
      { Buffer.add_string buf (lexeme lexbuf);
	string lexbuf }
  | '\\' _ 
      { lex_error lexbuf "unknown escape sequence in string" }
  | ['\n' '\r']
      { (* no \n anymore in strings since java 1.4 *)
	lex_error lexbuf "string not terminated"; }
  | [^ '\n' '\\' '"']+ 
      { Buffer.add_string buf (lexeme lexbuf); string lexbuf }
  | eof
      { lex_error lexbuf "string not terminated" }

and comment = parse
  | "*/"                
      { () }
  | '\n'
      { newline lexbuf; comment lexbuf }
  | [^'*''\n']+             
      { comment lexbuf }
  | _                   
      { comment lexbuf }
  | eof                 
      { lex_error lexbuf "comment not terminated" }

and annot = parse
  | "*/"                
      { Buffer.contents buf }
  | '\n' 
      { newline lexbuf;  
	Buffer.add_string buf (lexeme lexbuf);
	annot lexbuf }
  | ('\n' space* as s)  '@'
      { newline lexbuf;  
	Buffer.add_string buf s;
	Buffer.add_char buf ' ';
	annot lexbuf }
  | [^'@''*''\n''/']+
      { Buffer.add_string buf (lexeme lexbuf);
	annot lexbuf }
  | _                   
      { Buffer.add_string buf (lexeme lexbuf);
	annot lexbuf }
  | eof
      { lex_error lexbuf "annotation not terminated" }

{

let dotdot_mem = ref false
 
let next_token lexbuf =
  if !dotdot_mem then
    begin
      dotdot_mem := false;
      DOTDOT
    end
  else
    begin
      try
	token lexbuf
      with
	Dotdot(n) ->
	  dotdot_mem := true;
	  INTEGER n
    end

  let parse f c =
    let lb = from_channel c in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = f };
    try
      Java_parser.compilation_unit next_token lb
    with Parsing.Parse_error ->
      Java_options.parsing_error (loc lb) ""

}

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
