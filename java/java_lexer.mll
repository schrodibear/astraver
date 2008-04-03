(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************

Lexer for JavaCard source files

VerifiCard Project - D�mons research team - LRI - Universit� Paris XI

$Id: java_lexer.mll,v 1.25 2008-04-03 13:09:56 marche Exp $

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
	  "assert", ASSERT;
	  "assigns", ASSIGNS;
	  "axiom", AXIOM;
	  "behavior", BEHAVIOR;
	  "boolean", BOOLEAN;
	  "break", BREAK;
	  "byte", BYTE;
	  (* "byvalue", BYVALUE; ??? *)
	  "case", CASE;
	  (* "cast", CAST; ??? *)
	  "catch", CATCH;
	  "char", CHAR;
	  "class", CLASS;
	  "const", CONST;
	  "continue", CONTINUE;
	  "decreases", DECREASES;
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
	  (* "future", FUTURE; ?? *)
	  (* "generic", GENERIC; ?? *)
	  "ghost", GHOST;
	  "goto", GOTO;
	  "if", IF;
	  "implements", IMPLEMENTS;
	  "import", IMPORT;
	  (* "inner", INNER; ?? *)
	  "instanceof", INSTANCEOF;
	  "int", INT;
	  "integer", INTEGER;
	  "interface", INTERFACE;
	  "invariant", INVARIANT;
	  "lemma", LEMMA;
	  "logic", LOGIC;
	  "long", LONG;
	  "loop_invariant", LOOP_INVARIANT;
	  "model", MODEL;
	  "native", NATIVE;
	  "new", NEW;
	  "non_null", NON_NULL;
	  "null", NULL;
	  "nullable", NULLABLE;
	  (* "operator", OPERATOR; ?? *)
	  (* "outer", OUTER; ?? *)
	  "package", PACKAGE;
	  "predicate", PREDICATE;
	  "private", PRIVATE;
	  "protected", PROTECTED;
	  "public", PUBLIC;
	  "reads", READS;
	  "real", REAL;
	  "requires", REQUIRES;
	  (* "rest", REST; ?? *)
	  "return", RETURN;
	  "short", SHORT;
	  "signals", SIGNALS;
	  "static", STATIC;
	  "strictfp", STRICTFP;
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
	  "type", TYPE;
	  (* "var", VAR; ??? *)
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
	[ "at", BSAT;
	  "exists", BSEXISTS ;
	  (* "fresh", BSFRESH ; *)
	  "forall", BSFORALL ;
	  "nothing", BSNOTHING;
	  (*
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
	  lex_error lexbuf ("unknown special keyword \\"^s)

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

  let pragma lexbuf id v =
    match id with
      | "AbstractDomain" ->
	  begin
	    Java_options.ai_domain :=
	      match v with
		| "None" -> Jc_env.AbsNone 
		| "Box" -> Jc_env.AbsBox 
		| "Oct" -> Jc_env.AbsOct 
		| "Pol" -> Jc_env.AbsPol 
		| _ -> lex_error lexbuf ("unknown abstract domain " ^ v)
	  end  
      | "AnnotationPolicy" ->
	  begin
	    Java_options.annotation_sem :=
	      match v with
		| "None" -> Jc_env.AnnotNone
		| "Invariants" -> Jc_env.AnnotInvariants
		| "WeakPre" -> Jc_env.AnnotWeakPre
		| "StrongPre" -> Jc_env.AnnotStrongPre
		| _ -> lex_error lexbuf ("unknown annotation policy " ^ v)
	  end  
      | "CheckArithOverflow" ->
	  begin
	    match String.lowercase v with	  
	      | "yes" -> Java_options.ignore_overflow := false
	      | "no" -> Java_options.ignore_overflow := true
	      | _ -> lex_error lexbuf "yes or no expected"
	  end  
      | "InvariantPolicy" ->
	  begin
	    Java_options.inv_sem :=
	      match v with	  
		| "None" -> Jc_env.InvNone
		| "Arguments" -> Jc_env.InvArguments
		| "Ownership" -> Jc_env.InvOwnership
		| _ -> lex_error lexbuf ("unknown invariant policy " ^ v)
	  end  
      | "NonNullByDefault" ->
	  begin
	    Java_options.non_null :=
	    match String.lowercase v with	  
	      | "all" -> Java_env.NonNullAll
	      | "fields" -> Java_env.NonNullFields
	      | "no" -> Java_env.NonNullNone 
	      | _ -> lex_error lexbuf "unknown non-null policy"
	  end  
      | _ -> lex_error lexbuf ("unknown pragma " ^ id)

}

let space = [' ' '\t' '\r' '']
let backslash_escapes =
  ['\\' '"' '\'' 'n' 't' 'b' 'r' 'f' ]
let rD = ['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rFS	= ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*


rule token = parse
  | space+
      { token lexbuf }
  | '\n' 
      { newline lexbuf; token lexbuf }
  | "//@+" space* ((rL | rD)+ as id) space* "=" 
        space* ((rL | rD)+ as v) space* '\n'
      { pragma lexbuf id v; newline lexbuf; token lexbuf } 
  | "/*@"               
      { let loc = lexeme_start_p lexbuf in
	Buffer.clear buf; ANNOT(loc, annot lexbuf) }
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
  | ".."
      { DOTDOT }
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
  | "==>"
      { EQEQGT }
  | "<==>"
      { LTEQEQGT }
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
  | "*=" 
      { ASSIGNOP Bmul }
  | "/=" 
      { ASSIGNOP Bdiv }
  | "%=" 
      { ASSIGNOP Bmod }
  | "+=" 
      { ASSIGNOP Badd }
  | "-=" 
      { ASSIGNOP Bsub }
  | "<<=" 
      { ASSIGNOP Blsl }
  | ">>=" 
      { ASSIGNOP Blsr }
  | ">>>=" 
      { ASSIGNOP Basr }
  | "&=" 
      { ASSIGNOP Bbwand }
  | "^=" 
      { ASSIGNOP Bbwxor }
  | "|=" 
      { ASSIGNOP Bbwor }
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

  | ('0' | ['1'-'9']rD*) ['l''L']? as n
      { INTCONSTANT n }

      (* octal constants *)

  | '0'['0'-'7']+ ['l''L']? as n         
      { INTCONSTANT n }

      (* hexadecimal constants *)

  | '0'['x''X']['0'-'9' 'A'-'F' 'a'-'f']+['l''L']? as n 
    { INTCONSTANT n }

      (* trick to deal with intervals like 0..10 *)

  | (rD+ as n) ".."         { raise (Dotdot n) }

      (* floating-point constants *)

  | rD+ '.' rD* (['e''E']['-''+']?rD+)? ['f''F''d''D'] ?
      { REALCONSTANT (lexeme lexbuf) }

  | '.' rD+ (['e''E']['-''+']?rD+)? ['f''F''d''D'] ?
      { REALCONSTANT (lexeme lexbuf) }

  | rD+ ['e''E'] ['-''+']?rD+ ['f''F''d''D'] ?
      { REALCONSTANT (lexeme lexbuf) }

      (* character constants *)

  | "'" _ "'" as s
      { CHARACTER s }

  | "'\\" backslash_escapes "'" as s
      { CHARACTER s }

  | "'\\" ['0'-'3'] ['0'-'7'] ['0'-'7'] "'" as s
      { CHARACTER s }

  | "'\\" ['0'-'7'] ['0'-'7'] "'" as s
      { CHARACTER s }

  | "'\\" ['0'-'7'] "'" as s
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
  | ('\n' space* as s) '@'
      { newline lexbuf;  
	Buffer.add_string buf s;
	Buffer.add_char buf ' ';
	annot lexbuf }
  | [^'@''*''\n''/']+
      { Buffer.add_string buf (lexeme lexbuf);
	annot lexbuf }
  | '@'
      { annot lexbuf }
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
      Format.eprintf "DOTDOT@.";
      DOTDOT
    end
  else
    begin
      try
	token lexbuf
      with
	Dotdot(n) ->
	  dotdot_mem := true;
	  INTCONSTANT n
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
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)
