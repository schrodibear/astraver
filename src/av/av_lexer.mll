(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)


(*i $Id: jc_lexer.mll,v 1.95 2010-02-19 15:51:08 marche Exp $ i*)

{
  open Ast
  open Parser
  open Lexing

  type location = Lexing.position * Lexing.position

  let loc lexbuf : location = (lexeme_start_p lexbuf, lexeme_end_p lexbuf)

  exception Lexical_error of location * string

  let lex_error lexbuf s =
    raise (Lexical_error(loc lexbuf,s))

  let buf = Buffer.create 1024

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  (* Update the current location with file name and line number. *)

  let update_loc lexbuf file line absolute chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with
      | None -> pos.pos_fname
      | Some s -> s
    in
    lexbuf.lex_curr_p <-
      { pos with
	  pos_fname = new_file;
	  pos_lnum = if absolute then line else pos.pos_lnum + line;
	  pos_bol = pos.pos_cnum - chars;
      }

  let builtins_table =
    let table = Hashtbl.create 17 in
    List.iter
      (fun (_ty,id,_whyid,_params) -> Hashtbl.add table id ())
      Common.builtin_logic_symbols;
    List.iter
      (fun (_ty,id,_whyid,_params,_) -> Hashtbl.add table id ())
      Common.builtin_function_symbols;
    table

  let special_id lexbuf s =
    try
      let () = Hashtbl.find builtins_table s in
      IDENTIFIER s
    with
	Not_found ->
	  lex_error lexbuf ("unknown special symbol "^s)

  exception Dotdot of string

  let pragma lexbuf id v =
    match id with
      | "FloatModel" ->
	  begin
	    Options.float_model :=
	      (match v with
	         | "math" -> Env.FMmath
		 | "defensive" -> Env.FMdefensive
		 | "full" -> Env.FMfull
		 | "multirounding" -> Env.FMmultirounding
		 | _ -> lex_error lexbuf ("unknown float model " ^ v))
	  end
      | "FloatRoundingMode" ->
	  begin
	    Options.current_rounding_mode :=
	      (match v with
		 | "nearestEven" -> Env.FRMNearestEven
		 | "down" -> Env.FRMDown
		 | "up" -> Env.FRMUp
		 | "toZero" -> Env.FRMToZero
		 | "nearestAway" -> Env.FRMNearestAway
		 | _ -> lex_error lexbuf ("unknown float rounding mode " ^ v))
	  end
      | "FloatInstructionSet" ->
	  begin
	    Options.float_instruction_set :=
	      (match v with
		 | "x87" -> Env.FISx87
		 | "ieee754" -> Env.FISstrictIEEE754
		 | _ -> lex_error lexbuf ("unknown float instruction set " ^ v))
	  end
      | _ -> lex_error lexbuf ("unknown pragma " ^ id)

 let float_suffix = function
    | None -> `Real
    | Some('f' | 'F') -> `Single
    | Some('d' | 'D') -> `Double
    | _ -> assert false

}

let space = [' ' '\t' '\012' '\r']
let backslash_escapes =
  ['\\' '"' '\'' 'n' 't' 'b' 'r' 'f' ]
let rD = ['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rP = ['P''p']['+''-']? rD+
(*
 let rFS	= ('f'|'F'|'l'|'L')
*)
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | [' ' '\t' '\012' '\r']+ { token lexbuf }
  | '\n'                    { newline lexbuf; token lexbuf }
  | "/*@" | "//@"           { lex_error lexbuf "annotations should not be in @ comments" }
  | "/*"                    { comment lexbuf; token lexbuf }
  | "//" [^ '\n']* '\n'     { newline lexbuf; token lexbuf }
  | "abstract"              { ABSTRACT }
  | "allocates"             { ALLOCATES }
  | "and"                   { AND }
  | "as"                    { AS }
  | "assert"                { ASSERT }
  | "assume"                { ASSUME }
  | "assigns"               { ASSIGNS }
  | "assumes"               { ASSUMES }
  | "axiom"                 { AXIOM }
  | "axiomatic"             { AXIOMATIC }
  | "behavior"              { BEHAVIOR }
  | "boolean"               { BOOLEAN }
  | "break"                 { BREAK }
  | "case"                  { CASE }
  | "catch"                 { CATCH }
  | "check"                 { CHECK }
  | "continue"              { CONTINUE }
  | "decreases"             { DECREASES }
  | "default"               { DEFAULT }
  | "do"                    { DO }
  | "double"                { Options.has_floats := true; DOUBLE }
  | "else"                  { ELSE }
  | "end"                   { END }
  | "ensures"               { ENSURES }
  | "exception"             { EXCEPTION }
  | "false"                 { CONSTANT (JCCboolean false) }
  | "finally"               { FINALLY }
  | "float"                 { Options.has_floats := true; FLOAT }
  | "for"                   { FOR }
  | "free"                  { FREE }
  | "goto"                  { GOTO }
  | "hint"                  { HINT }
  | "if"                    { IF }
  | "in"                    { IN }
  | "integer"               { INTEGER }
  | "invariant"             { INVARIANT }
  | "lemma"                 { LEMMA }
  | "let"                   { LET }
  | "logic"                 { LOGIC }
  | "loop"                  { LOOP }
  | "match"                 { MATCH }
  | "new"                   { NEW }
  | "null"                  { NULL }
  | "of"                    { OF }
  | "pack"                  { PACK }
  | "predicate"             { PREDICATE }
  | "reads"                 { READS }
  | "real"                  { REAL}
  | "reinterpret"           { REINTERPRET }
  | "rep"                   { REP }
  | "requires"              { REQUIRES }
  | "return"                { RETURN }
  | "switch"                { SWITCH }
  | "tag"                   { TAG }
  | "then"                  { THEN }
  | "throw"                 { THROW }
  | "throws"                { THROWS }
  | "true"                  { CONSTANT (JCCboolean true) }
  | "try"                   { TRY }
  | "type"                  { TYPE }
  | "unit"                  { UNIT }
  | "unpack"                { UNPACK }
  | "var"                   { VAR }
  | "variant"               { VARIANT }
  | "while"                 { WHILE }
  | "with"                  { WITH }
  | "\\absolute_address"    { BSABSOLUTE_ADDRESS }
  | "\\address"             { BSADDRESS }
  | "\\at"                  { BSAT }
  | "\\base_block"          { BSBASE_BLOCK }
  | "\\bottom"              { BSBOTTOM }
  | "\\exists"              { BSEXISTS }
  | "\\forall"              { BSFORALL }
  | "\\fresh"               { BSFRESH }
  | "\\allocable"           { BSALLOCABLE }
  | "\\freeable"            { BSFREEABLE }
  | "\\mutable"             { BSMUTABLE }
  | "\\nothing"             { BSNOTHING }
  | "\\offset_max"          { BSOFFSET_MAX }
  | "\\offset_min"          { BSOFFSET_MIN }
  | "\\old"                 { BSOLD }
  | "\\result"              { BSRESULT }
  | "\\typeeq"              { BSTYPEEQ }
  | "\\typeof"              { BSTYPEOF }
  | "\\" rL (rL | rD)* as s { special_id lexbuf s }
(*
  | "#" [' ' '\t']* (['0'-'9']+ as num) [' ' '\t']*
        ("\"" ([^ '\010' '\013' '"' ] * as name) "\"")?
        [^ '\010' '\013'] * '\n'
      { update_loc lexbuf name (int_of_string num) true 0;
        token lexbuf }
  | '#' [^'\n']* '\n'       { newline lexbuf; token lexbuf }
*)
  | '#' space* ((rL | rD)+ as id) space* "="
        space* ((rL | rD)+ as v) space* '\n'
      { pragma lexbuf id v; newline lexbuf; token lexbuf }
  | rL (rL | rD)*           { match lexeme lexbuf with
				| "_" -> UNDERSCORE
				| s -> IDENTIFIER s }

  | '0'['x''X'] rH+ rIS?    { CONSTANT (JCCinteger (lexeme lexbuf)) }
  | '0' rD+ rIS?            { CONSTANT (JCCinteger (lexeme lexbuf)) }
  | rD+ rIS?                { CONSTANT (JCCinteger (lexeme lexbuf)) }
  | 'L'? "'" [^ '\n' '\'']+ "'"     { CONSTANT (JCCinteger (lexeme lexbuf)) }

  | ('0'['x''X'] rH+ '.' rH* rP) as pre
  | ('0'['x''X'] rH* '.' rH+ rP) as pre
  | ('0'['x''X'] rH+ rP) as pre
  | (rD+ rE) as pre
  | (rD* "." rD+ (rE)?) as pre
  | (rD+ "." rD* (rE)?) as pre
      { CONSTANT (JCCreal pre) }

      (* trick to deal with intervals like 0..10 *)

  | (rD+ as n) ".."         { raise (Dotdot n) }

      (* character constants *)

  | '"'                     { Buffer.clear buf; STRING_LITERAL(string lexbuf) }
  | ">>>"                   { ARSHIFT }
  | ">>"                    { LRSHIFT }
  | "<<"                    { LSHIFT }
  | "<<%"                   { LSHIFTM }
  | "&&"                    { AMPAMP }
  | "||"                    { BARBAR }
  | "==>"                   { EQEQGT }
  | "<==>"                  { LTEQEQGT }
  | "<="                    { LTEQ }
  | ">="                    { GTEQ }
  | "=="                    { EQEQ }
  | "!="                    { BANGEQ }
  | ";"                     { SEMICOLON }
  | ";;"                    { SEMISEMI }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | ","                     { COMMA }
  | ":"                     { COLON }
  | "="                     { EQ }
  | "()"                    { LPARRPAR }
  | "("                     { LPAR }
  | ")"                     { RPAR }
  | "["                     { LSQUARE }
  | "]"                     { RSQUARE }
  | "."                     { DOT }
  | ".."                    { DOTDOT }
  | "..."                   { DOTDOTDOT }
  | "<:"                    { LTCOLON }
  | ":>"                    { COLONGT }
  | ":%>"                   { COLONPGT }
  | "&"                     { AMP }
  | "!"                     { EXCLAM }
  | "~"                     { TILDE }
  | "-"                     { MINUS }
  | "-%"                    { MINUSM }
  | "+"                     { PLUS }
  | "+%"                    { PLUSM }
  | "*"                     { STAR }
  | "*%"                    { STARM }
  | "/"                     { SLASH }
  | "/%"                    { SLASHM }
  | "%"                     { PERCENT }
  | "<"                     { LT }
  | ">"                     { GT }
  | "^"                     { HAT }
  | "|"                     { PIPE }
  | "?"                     { QUESTION }
  | "@"                     { AT }
  | "->"                    { MINUSGT }
  | eof { EOF }
  | '"' { lex_error lexbuf "unterminated string" }
  | _   { lex_error lexbuf ("illegal character " ^ lexeme lexbuf) }

and comment = parse
  | "*/" { () }
  | "/*" { comment lexbuf ; comment lexbuf }
  | eof  { lex_error lexbuf "unterminated comment" }
  | '\n' { newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }

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
	  CONSTANT(JCCinteger n)
    end

  let parse f c =
    let lb = from_channel c in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = f };
    try
      Parser.file next_token lb
    with Parsing.Parse_error ->
      Options.parsing_error (loc lb) ""

}


(*
Local Variables:
compile-command: "make -C .. bin/jessie.byte"
End:
*)
