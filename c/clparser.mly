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

  open Cast
  open Clogic

  let loc () = (symbol_start (), symbol_end ())
  let loc_i i = (rhs_start i, rhs_end i)
  let info x = { Clogic.node = x; info = loc () }
  let info_i i x = { Clogic.node = x; info = loc_i i }

%}

%token <string> IDENTIFIER CONSTANT STRING_LITERAL
%token LPAR RPAR IF ELSE COLON DOT INT FLOAT LT GT LE GE EQ NE COMMA ARROW
%token FORALL EXISTS IMPLIES AND OR NOT 
%token TRUE FALSE OLD AT RESULT LENGTH VALID THEN AT
%token QUESTION MINUS PLUS STAR AMP SLASH PERCENT LSQUARE RSQUARE EOF
%token INVARIANT VARIANT DECREASES FOR LABEL ASSERT SEMICOLON NULL
%token REQUIRES ENSURES ASSIGNS READS LOGIC PREDICATE AXIOM LBRACE RBRACE

%nonassoc prec_forall prec_exists
%right IMPLIES
%left OR
%left AND
%nonassoc prec_not
%nonassoc prec_if
%nonassoc prec_relation

%right QUESTION prec_question
%left PLUS MINUS
%left STAR SLASH PERCENT
%right prec_uminus 
%left DOT ARROW LSQUARE

%type <Cast.parsed_annot> annot
%start annot

%%

predicate:
  predicate IMPLIES predicate { Pimplies ($1, $3) }
| predicate OR predicate     { Por ($1, $3) }
| predicate AND predicate    { Pand ($1, $3) }
| NOT predicate %prec prec_not { Pnot $2 }
| TRUE { Ptrue }
| FALSE { Pfalse }
| IDENTIFIER { Papp (loc (), Info.default_logic_info $1, []) }
| IDENTIFIER LPAR term_list RPAR 
      { Papp (loc_i 1, Info.default_logic_info $1, $3) }
| term relation term %prec prec_relation { Prel ($1, $2, $3) }
| term relation term relation term %prec prec_relation 
      { Pand (Prel ($1, $2, $3), Prel ($3, $4, $5)) }
| IF term THEN predicate ELSE predicate %prec prec_if
      { Pif ($2, $4, $6) }
| FORALL ne_parameters SEMICOLON predicate %prec prec_forall
      { Pforall ($2, $4) }
| EXISTS ne_parameters SEMICOLON predicate %prec prec_exists
      { Pexists ($2, $4) }
| LPAR predicate RPAR { $2 }
| VALID LPAR term COMMA term COMMA term RPAR { Pvalid ($3,$5,$7) }
;

logic_type:
  IDENTIFIER { LTvar $1 }
| INT        { LTint }
| FLOAT      { LTfloat }
| logic_type LSQUARE RSQUARE { LTarray $1 }
| logic_type STAR { LTpointer $1 }
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
  NULL { info Tnull } 
| CONSTANT { info (Tconstant $1) }
| IDENTIFIER { info (Tvar (Info.default_var_info $1)) }
| IDENTIFIER LPAR term_list RPAR 
    { info (Tapp (Info.default_logic_info $1, $3)) }
| term PLUS term { info (Tbinop ($1, Badd, $3)) }
| term MINUS term { info (Tbinop ($1, Bsub, $3)) }
| term STAR term { info (Tbinop ($1, Bmul, $3)) }
| term SLASH term { info (Tbinop ($1, Bdiv, $3)) }
| term PERCENT term { info (Tbinop ($1, Bmod, $3)) }
| term ARROW IDENTIFIER { info (Tarrow ($1, $3)) }
| term DOT IDENTIFIER { info (Tdot ($1, $3)) }
| term LSQUARE term RSQUARE { info (Tarrget ($1, $3)) }
| MINUS term %prec prec_uminus { info (Tunop (Uminus, $2)) }
| PLUS term %prec prec_uminus { $2 }
| STAR term { info (Tunop (Ustar, $2)) }
| term QUESTION term COLON term %prec prec_question { info (Tif ($1, $3, $5)) }
| OLD LPAR term RPAR { info (Told $3) }
| AT LPAR term COMMA IDENTIFIER RPAR { info (Tat ($3, $5)) }
| LENGTH LPAR term RPAR { info (Tlength $3) }
| RESULT { info Tresult }
/* | LPAR term RPAR { $2 } */
/* | LPAR logic_type RPAR term { info (Tcast ($2, $4)) } */
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
| REQUIRES predicate { Some $2 }
;

post_condition:
  /* epsilon */  { None }
| ENSURES predicate { Some $2 }
;

spec:
  pre_condition effects post_condition decreases 
    { { requires = $1; assigns = $2; ensures = $3; decreases = $4 } }
;

loop_annot:
  invariant variant { { invariant = Some $1; variant = Some $2 } }
| variant { { invariant = None; variant = Some $1 } }
| invariant { { invariant = Some $1; variant = None } }
;

invariant:
| INVARIANT predicate { $2 }
;

variant:
  VARIANT term FOR IDENTIFIER { ($2, Some $4) }
| VARIANT term                { ($2, None) }
;

decreases:
  /* epsilon */   { None }
| DECREASES variant { Some $2 }
;

annot: 
  annotation EOF   { $1 }
;

annotation:
  decl             { Adecl $1 }
| spec             { Aspec $1 }
| loop_annot       { Aloop_annot $1 }
| ASSERT predicate { Acode_annot (Assert $2) }
| LABEL IDENTIFIER { Acode_annot (Label $2) }
;

effects:
  /* epsilon */ { [] }
| ASSIGNS locations { $2 }
;

locations:
| location { [$1] }
| location COMMA locations { $1 :: $3 }
;

location:
  location_term { Lterm $1 }
| location_term LSQUARE STAR RSQUARE { Lstar $1 }
| location_term LSQUARE location_term DOT DOT location_term RSQUARE    
   { Lrange ($1, $3, $6) }
;

location_term:
| IDENTIFIER { info (Tvar (Info.default_var_info $1)) }
| location_term ARROW IDENTIFIER { info (Tarrow ($1, $3)) }
| location_term DOT IDENTIFIER { info (Tdot ($1, $3)) }
| location_term LSQUARE location_term RSQUARE { info (Tarrget ($1, $3)) }
| STAR location_term { info (Tunop (Ustar, $2)) }
;

decl:
  LOGIC logic_type IDENTIFIER LPAR parameters RPAR 
    { LDlogic (Info.default_logic_info $3, $2, $5, []) }
| LOGIC logic_type IDENTIFIER LPAR parameters RPAR READS locations 
    { LDlogic (Info.default_logic_info $3, $2, $5, $8) }
| PREDICATE IDENTIFIER LPAR parameters RPAR 
    { LDpredicate_reads (Info.default_logic_info $2, $4, []) }
| PREDICATE IDENTIFIER LPAR parameters RPAR READS locations 
    { LDpredicate_reads (Info.default_logic_info $2, $4, $7) }
| PREDICATE IDENTIFIER LPAR parameters RPAR LBRACE predicate RBRACE 
    { LDpredicate_def (Info.default_logic_info $2, $4, $7) }
| AXIOM IDENTIFIER COLON predicate { LDaxiom ($2, $4) }
;

parameters:
  /* epsilon */  { [] }
| ne_parameters { $1 }
;

ne_parameters:
  logic_type IDENTIFIER { [($1, $2)] }
| logic_type IDENTIFIER COMMA ne_parameters { ($1,$2) :: $4 }
;

%%
