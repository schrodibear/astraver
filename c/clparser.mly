/*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 */

/* Grammar for C annotations */

%{

  open Clogic

  let loc () = (symbol_start (), symbol_end ())
  let info x = { Clogic.node = x; info = loc () }

%}

%token <string> IDENTIFIER CONSTANT STRING_LITERAL
%token LPAR RPAR IF ELSE COLON DOT INT FLOAT LT GT LE GE EQ NE COMMA ARROW
%token FORALL EXISTS AND OR NOT TRUE FALSE OLD RESULT LENGTH THEN AT
%token QUESTION MINUS PLUS STAR SLASH PERCENT LSQUARE RSQUARE EOF

%right ARROW
%left OR
%left AND
%nonassoc prec_not
%nonassoc prec_if prec_forall prec_exists

%type <Loc.t Clogic.predicate> predicate
%start predicate

%%

predicate:
  predicate ARROW predicate { info (Pimplies ($1, $3)) }
| predicate OR predicate     { info (Por ($1, $3)) }
| predicate AND predicate    { info (Pand ($1, $3)) }
| NOT predicate              { info (Pnot $2) }
| TRUE { info Ptrue }
| FALSE { info Pfalse }
| IDENTIFIER { info (Pvar $1) }
| IDENTIFIER LPAR term_list RPAR { info (Papp ($1, $3)) }
| term relation term { info (Prel ($1, $2, $3)) }
| term relation term relation term { info 
				       (Pand (info (Prel ($1, $2, $3)),
					      info (Prel ($3, $4, $5)))) }
| IF term THEN predicate ELSE predicate %prec prec_if
      { info (Pif ($2, $4, $6)) }
| FORALL IDENTIFIER COLON pure_type DOT predicate %prec prec_forall
      { info (Pforall ($2, $4, $6)) }
| EXISTS IDENTIFIER COLON pure_type DOT predicate %prec prec_exists
      { info (Pexists ($2, $4, $6)) }
| LPAR predicate RPAR { $2 }
;

pure_type:
  IDENTIFIER { PTexternal ([], $1) }
| INT        { PTint }
| FLOAT      { PTfloat }
;

relation:
  | LT    { Lt } 
  | GT    { Gt }
  | LE    { Le }
  | GE    { Ge }
  | EQ    { Eq }
  | NE    { Neq }
;

term:
| IDENTIFIER { info (Tvar ($1, Current)) }
| IDENTIFIER AT { info (Tvar ($1, Before)) }
| IDENTIFIER AT IDENTIFIER { info (Tvar ($1, At $3)) }
| IDENTIFIER LPAR term_list RPAR { info (Tapp ($1, $3)) }
;

term_list:
| /* epsilon */ { [] }
| ne_term_list  { $1 }
;

ne_term_list:
| term                    { [$1] }
| term COMMA ne_term_list { $1 :: $3 }
;

%%

(***
(* Entries for the C parser *)

type 'a c_parser = int -> string -> 'a

val parse_c_spec : (lexpr asst list * Effect.t * lexpr post option) c_parser
val parse_c_pre : (lexpr asst option * variant option) c_parser
val parse_c_post : (lexpr post option) c_parser
val parse_c_loop_annot : (lexpr asst option * variant) c_parser
val parse_c_decl : decl c_parser
val parse_c_annot : block_st c_parser
***)

(***

let c_pre_condition = gec "c_pre_condition"
let c_post_condition = gec "c_post_condition"
let c_spec = gec "c_spec"
let c_loop_annot = gec "c_loop_annot"
let c_pre = gec "c_pre"
let c_variant = gec "c_variant"
let c_post = gec "c_post"
let c_annot = gec "c_annot"

EXTEND
  c_pre_condition:
  [ [ LIDENT "pre"; p = pre_condition -> p ] ];
  c_post_condition:
  [ [ LIDENT "post"; q = post_condition -> q ] ];
  c_spec:
  [ [ p = OPT c_pre_condition; e = effects; q = OPT c_post_condition; EOI -> 
      (list_of_some p, e, q)
  ] ];
  c_loop_annot:
  [ [ i = OPT invariant; LIDENT "variant"; v = variant -> i,v
  ] ];
  c_pre:
  [ [ p = OPT pre_condition; v = OPT c_variant -> p,v ] ];
  c_variant:
  [ [ LIDENT "variant"; v = variant -> v ] ];
  c_post:
  [ [ q = OPT post_condition -> q ] ];
  c_annot:
  [ [ LIDENT "assert"; p = assertion -> Sassert p 
    | LIDENT "label"; s = ident -> Slabel (Ident.string s) ] ];
END
;;

type 'a c_parser = int -> string -> 'a

let parse_with_offset f n s =
  (* Options.if_debug_3 Format.eprintf "parse_with_offset : %d %s@\n" n s; *)
  let st = Stream.of_string s in
  with_offset n (Grammar.Entry.parse f) st

let parse_c_spec = parse_with_offset c_spec
let parse_c_pre = parse_with_offset c_pre
let parse_c_post = parse_with_offset c_post
let parse_c_loop_annot = parse_with_offset c_loop_annot
let parse_c_decl = parse_with_offset decl
let parse_c_annot = parse_with_offset c_annot

***)

