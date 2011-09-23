/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2011                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           */
/*    Yannick MOY, Univ. Paris-sud 11                                     */
/*    Romain BARDOU, Univ. Paris-sud 11                                   */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
/*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     */
/*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          */
/*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        */
/*    Sylvie BOLDO, INRIA                 (floating-point support)        */
/*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  */
/*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Lesser General Public            */
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

%{
  open Simplify_ast
  let at_true = Tapp ("at_true", [])
%}

%token <string> IDENT
%token <string> INTEGER
%token DEFPRED BG_PUSH AT_TRUE TRUE FALSE AND IMPLIES EXPLIES IFF FORALL EXISTS 
%token MPAT PATS NOPATS AND OR NOT LBLPOS LBLNEG DISTINCT EQ NEQ LT LE GT GE
%token LPAR RPAR EOF

%type <Simplify_ast.t> start
%start start

%%

start: 
  list0_decl EOF { $1 }
;

list0_decl:
  /* epsilon */ { [] }
| list1_decl    { $1 }
;

list1_decl:
  decl { $1 }
| decl list1_decl { $1 @ $2 }
;
 
decl:
| LPAR BG_PUSH predicate RPAR
    { match $3 with
      | Pand l -> List.map (fun p -> Axiom p) l
      | p -> [Axiom p] }
| LPAR DEFPRED LPAR list1_ident RPAR RPAR
    { [] }
| LPAR DEFPRED LPAR list1_ident RPAR predicate RPAR
    { [Defpred (List.hd $4, List.tl $4, $6)] }
| predicate
    { [Goal $1] }
;

list1_predicate:
  predicate { [$1] }
| predicate list1_predicate { $1 :: $2 }
;

predicate:
  TRUE { Ptrue }
| FALSE { Pfalse }
| LPAR AND list1_predicate RPAR { Pand $3 }
| LPAR OR list1_predicate RPAR { Por $3 }
| LPAR IMPLIES predicate predicate RPAR { Pimplies ($3, $4) }
| LPAR EXPLIES predicate predicate RPAR { Pimplies ($3, $4) }
| LPAR IFF predicate predicate RPAR { Piff ($3, $4) }
| LPAR NOT predicate RPAR { Pnot $3 }
| LPAR EQ term term RPAR { Prel ($3, Eq, $4) }
| LPAR NEQ term term RPAR { Prel ($3, Neq, $4) }
| LPAR LT term term RPAR { Prel ($3, Lt, $4) }
| LPAR LE term term RPAR { Prel ($3, Le, $4) }
| LPAR GT term term RPAR { Prel ($3, Gt, $4) }
| LPAR GE term term RPAR { Prel ($3, Ge, $4) }
| LPAR DISTINCT list1_term RPAR { Pdistinct $3 }
| LPAR IDENT list1_term RPAR { Prel (Tapp ($2, $3), Eq, at_true) }
| IDENT { Prel (Tapp ($1, []), Eq, at_true) }
| LPAR FORALL LPAR list1_ident RPAR LPAR pats list1_trigger RPAR predicate RPAR
    { Pforall ($4, $8, $10) }
| LPAR FORALL LPAR list1_ident RPAR predicate RPAR
    { Pforall ($4, [], $6) }
| LPAR EXISTS LPAR list1_ident RPAR LPAR pats list1_trigger RPAR predicate RPAR
    { Pexists ($4, $8, $10) }
| LPAR EXISTS LPAR list1_ident RPAR predicate RPAR
    { Pexists ($4, [], $6) }
| LPAR predicate RPAR { $2 }
| LPAR LBLPOS IDENT predicate RPAR { Plblpos ($3, $4) }
| LPAR LBLNEG IDENT predicate RPAR { Plblneg ($3, $4) }
;

pats:
| PATS  { () }
| NOPATS { () }
;

list1_trigger:
  trigger { [$1] }
| trigger list1_trigger { $1 :: $2 }
;

trigger:
  LPAR MPAT list1_term RPAR { $3 }
| term { [$1] }
/* should be allowed as a pattern
| LPAR NEQ term term RPAR { [Prel ($3, Neq, $4)] }
*/;

term:
  LPAR term RPAR { $2 }
| INTEGER { Tconst $1 }
| IDENT { Tapp ($1, []) }
| LPAR IDENT list1_term RPAR { Tapp ($2, $3) }
| AT_TRUE { at_true }
;

list1_term:
  term { [$1] }
| term list1_term { $1 :: $2 }
;

list1_ident:
  IDENT { [$1] }
| IDENT list1_ident { $1 :: $2 }
;
