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
  let info x = { Clogic.lexpr_node = x; lexpr_loc = loc () }

%}

%token <string> IDENTIFIER CONSTANT STRING_LITERAL
%token LPAR RPAR IF ELSE COLON DOT INT FLOAT LT GT LE GE EQ NE COMMA ARROW
%token FORALL EXISTS IMPLIES AND OR NOT 
%token TRUE FALSE OLD AT RESULT LENGTH VALID VALID_RANGE THEN AT
%token QUESTION MINUS PLUS STAR AMP SLASH PERCENT LSQUARE RSQUARE EOF
%token INVARIANT VARIANT DECREASES FOR LABEL ASSERT SEMICOLON NULL
%token REQUIRES ENSURES ASSIGNS READS LOGIC PREDICATE AXIOM LBRACE RBRACE

%nonassoc prec_forall prec_exists
%right IMPLIES
%left OR
%left AND
%nonassoc prec_not
%nonassoc prec_if
%left prec_relation LT GT LE GE EQ NE
%right QUESTION prec_question
%left PLUS MINUS
%left STAR SLASH PERCENT
%right prec_uminus 
%left DOT ARROW LSQUARE

%type <Cast.parsed_annot> annot
%start annot

%%

lexpr:
  /* predicates */
  lexpr IMPLIES lexpr { info (PLimplies ($1, $3)) }
| lexpr OR lexpr     { info (PLor ($1, $3)) }
| lexpr AND lexpr    { info (PLand ($1, $3)) }
| NOT lexpr %prec prec_not { info (PLnot $2) }
| TRUE { info PLtrue }
| FALSE { info PLfalse }
| lexpr relation lexpr %prec prec_relation { info (PLrel ($1, $2, $3)) }
| IF lexpr THEN lexpr ELSE lexpr %prec prec_if
      { info (PLif ($2, $4, $6)) }
| FORALL ne_parameters SEMICOLON lexpr %prec prec_forall
      { info (PLforall ($2, $4)) }
| EXISTS ne_parameters SEMICOLON lexpr %prec prec_exists
      { info (PLexists ($2, $4)) }
| VALID LPAR lexpr RPAR { info (PLvalid ($3)) }
| VALID_RANGE LPAR lexpr COMMA lexpr COMMA lexpr RPAR 
      { info (PLvalid_range ($3,$5,$7)) }
/* terms */
| NULL { info PLnull } 
| CONSTANT { info (PLconstant $1) }
| lexpr PLUS lexpr { info (PLbinop ($1, Badd, $3)) }
| lexpr MINUS lexpr { info (PLbinop ($1, Bsub, $3)) }
| lexpr STAR lexpr { info (PLbinop ($1, Bmul, $3)) }
| lexpr SLASH lexpr { info (PLbinop ($1, Bdiv, $3)) }
| lexpr PERCENT lexpr { info (PLbinop ($1, Bmod, $3)) }
| lexpr ARROW IDENTIFIER { info (PLarrow ($1, $3)) }
| lexpr DOT IDENTIFIER { info (PLdot ($1, $3)) }
| lexpr LSQUARE lexpr RSQUARE { info (PLarrget ($1, $3)) }
| MINUS lexpr %prec prec_uminus { info (PLunop (Uminus, $2)) }
| PLUS lexpr %prec prec_uminus { $2 }
| STAR lexpr { info (PLunop (Ustar, $2)) }
| lexpr QUESTION lexpr COLON lexpr %prec prec_question 
    { info (PLif ($1, $3, $5)) }
| OLD LPAR lexpr RPAR { info (PLold $3) }
| AT LPAR lexpr COMMA IDENTIFIER RPAR { info (PLat ($3, $5)) }
| LENGTH LPAR lexpr RPAR { info (PLlength $3) }
| RESULT { info PLresult }
/***
| LPAR logic_type RPAR lexpr { info (PLcast ($2, $4)) }
***/
/* both terms and predicates */
| LPAR lexpr RPAR { $2 }
| IDENTIFIER { info (PLvar (Info.default_var_info $1)) }
| IDENTIFIER LPAR lexpr_list RPAR 
    { info (PLapp (Info.default_logic_info $1, $3)) }
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

lexpr_list:
| /* epsilon */ { [] }
| ne_lexpr_list  { $1 }
;

ne_lexpr_list:
| lexpr                    { [$1] }
| lexpr COMMA ne_lexpr_list { $1 :: $3 }
;

pre_condition:
  /* epsilon */ { None }
| REQUIRES lexpr { Some $2 }
;

post_condition:
  /* epsilon */  { None }
| ENSURES lexpr { Some $2 }
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
| INVARIANT lexpr { $2 }
;

variant:
  VARIANT lexpr FOR IDENTIFIER { ($2, Some $4) }
| VARIANT lexpr                { ($2, None) }
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
| ASSERT lexpr { Acode_annot (Assert $2) }
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
| IDENTIFIER { info (PLvar (Info.default_var_info $1)) }
| location_term ARROW IDENTIFIER { info (PLarrow ($1, $3)) }
| location_term DOT IDENTIFIER { info (PLdot ($1, $3)) }
| location_term LSQUARE location_term RSQUARE { info (PLarrget ($1, $3)) }
| STAR location_term { info (PLunop (Ustar, $2)) }
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
| PREDICATE IDENTIFIER LPAR parameters RPAR LBRACE lexpr RBRACE 
    { LDpredicate_def (Info.default_logic_info $2, $4, $7) }
| AXIOM IDENTIFIER COLON lexpr { LDaxiom ($2, $4) }
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
