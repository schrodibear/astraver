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
%token FORALL EXISTS IMPLIES AND OR NOT TRUE FALSE OLD RESULT LENGTH THEN AT
%token QUESTION MINUS PLUS STAR SLASH PERCENT LSQUARE RSQUARE EOF
%token INVARIANT VARIANT FOR LABEL ASSERT PRE POST READS WRITES

%right IMPLIES
%left OR
%left AND
%nonassoc prec_not
%nonassoc prec_if prec_forall prec_exists
%nonassoc prec_relation

%right QUESTION prec_question
%left PLUS MINUS
%left STAR SLASH PERCENT
%right prec_uminus 
%left DOT ARROW

%type <Loc.t Clogic.predicate> predicate
%start predicate

%type <Loc.t Clogic.spec> spec
%start spec

%type <Loc.t Clogic.loop_annot> loop_annot
%start loop_annot

%%

predicate:
  predicate IMPLIES predicate { info (Pimplies ($1, $3)) }
| predicate OR predicate     { info (Por ($1, $3)) }
| predicate AND predicate    { info (Pand ($1, $3)) }
| NOT predicate %prec prec_not { info (Pnot $2) }
| TRUE { info Ptrue }
| FALSE { info Pfalse }
| IDENTIFIER { info (Pvar $1) }
| IDENTIFIER LPAR term_list RPAR { info (Papp ($1, $3)) }
| term relation term %prec prec_relation { info (Prel ($1, $2, $3)) }
| term relation term relation term %prec prec_relation 
      { info (Pand (info (Prel ($1, $2, $3)),
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
| CONSTANT { info (Tconstant $1) }
| IDENTIFIER { info (Tvar ($1, Current)) }
| IDENTIFIER AT { info (Tvar ($1, Before)) }
| IDENTIFIER AT IDENTIFIER { info (Tvar ($1, At $3)) }
| IDENTIFIER LPAR term_list RPAR { info (Tapp ($1, $3)) }
| term PLUS term { info (Tbinop ($1, Badd, $3)) }
| term MINUS term { info (Tbinop ($1, Bsub, $3)) }
| term STAR term { info (Tbinop ($1, Bmul, $3)) }
| term SLASH term { info (Tbinop ($1, Bdiv, $3)) }
| term PERCENT term { info (Tbinop ($1, Bmod, $3)) }
| term ARROW IDENTIFIER { info (Tarrow ($1, $3)) }
| term DOT IDENTIFIER { info (Tdot ($1, $3)) }
| MINUS term %prec prec_uminus { info (Tunop (Uminus, $2)) }
| PLUS term %prec prec_uminus { $2 }
| STAR term { info (Tunop (Ustar, $2)) }
| term QUESTION term COLON term %prec prec_question { info (Tif ($1, $3, $5)) }
;

term_list:
| /* epsilon */ { [] }
| ne_term_list  { $1 }
;

ne_term_list:
| term                    { [$1] }
| term COMMA ne_term_list { $1 :: $3 }
;

pre_condition:
  /* epsilon */ { None }
| PRE predicate { Some $2 }
;

post_condition:
  /* epsilon */  { None }
| POST predicate { Some $2 }
;

spec:
  pre_condition effects post_condition EOF { ($1, $2, $3) }
;

loop_annot:
  invariant VARIANT variant { ($1, $3) }
;

invariant:
  /* epsilon */       { None }
| INVARIANT predicate { Some $2 }
;

pre:
  pre_condition opt_variant { ($1, $2) }
;

variant:
  term FOR IDENTIFIER { ($1, Some $3) }
| term                { ($1, None) }
;

opt_variant:
  /* epsilon */   { None }
| VARIANT variant { Some $2 }
;

annot:
  ASSERT predicate { Assert $2 }
| LABEL IDENTIFIER { Label $2 }
;

effects:
  reads writes { ($1, $2) }
;

reads:
  /* epsilon */    { [] }
| READS ident_list { $2 }
;

writes:
  /* epsilon */    { [] }
| WRITES ident_list { $2 }
;

ident_list:
  /* epsilon */    { [] }
| ne_ident_list    { $1 }
;

ne_ident_list:
  IDENTIFIER                     { [$1] }
| IDENTIFIER COMMA ne_ident_list { $1 :: $3 }
;

%%
