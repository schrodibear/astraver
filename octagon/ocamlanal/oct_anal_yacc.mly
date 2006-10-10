/* oct_anal_yacc.mly
   Parser for the toy language for the example analyzer.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
*/


%{
open Oct_anal_syn
%}

/* tokens */
%token T_LPAR T_RPAR T_BRAND T_RAND T_ASSERT
%token T_PROG T_WHILE T_IF
%token T_UMINUS T_UPLUS
%token T_PLUS T_MINUS T_TIMES T_LEQ T_GEQ T_L T_G T_EQ T_NEQ
%token T_AND T_OR T_NOT
%token <float> T_NUM
%token <string> T_ID
%token <int> T_BEGINPROG T_ENDPROG
%token <int> T_DO T_DONE T_THEN T_ELSE T_BEGIN T_END T_SEMICOLON
%token T_TRUE T_FALSE
%token T_EOF

/* precedence */
%nonassoc T_SEMICOLON
%nonassoc T_WHILE T_DO T_DONE T_ASSERT
%nonassoc T_IF T_THEN
%nonassoc T_ELSE
%nonassoc T_LPAR T_RPAR T_BEGIN T_END
%left T_OR
%left T_AND
%nonassoc T_NOT
%nonassoc T_LEQ T_GEQ T_L T_G T_EQ T_NEQ
%left T_PLUS T_MINUS
%left T_TIMES
%nonassoc T_UMINUS

/* types */
%type <Oct_anal_syn.prog list> proglist
%type <Oct_anal_syn.comp>  comp
%type <Oct_anal_syn.bexpr> bexpr
%type <Oct_anal_syn.inst>  inst
%type <Oct_anal_syn.block>  instlist
%type <Oct_anal_syn.block>  block
%type <Oct_anal_syn.iexpr> iexpr

%start proglist
%%

comp :
  T_LEQ { LESSEQ }
| T_GEQ { GREATEREQ }
| T_L   { LESS }
| T_G   { GREATER }
| T_EQ  { EQ }
| T_NEQ { NOTEQ }

bexpr :
  T_LPAR bexpr T_RPAR                   { $2 }
| bexpr T_AND bexpr                     { AND ($1,$3) }
| bexpr T_OR  bexpr                     { OR  ($1,$3) }
| T_NOT bexpr                           { NOT  $2 }
| iexpr comp iexpr                      { COMP ($2,$1,$3) }
|                                       { TRUE }
| T_TRUE                                { TRUE }
| T_FALSE                               { FALSE }
| T_BRAND                               { BRAND }

inst :
  T_WHILE bexpr T_DO instlist T_DONE     
{ LOOP ($2,set_end_block (set_start_block $4 $3) $5) }

| T_IF bexpr T_THEN block 
{ IF ($2,set_start_block $4 $3) }

| T_IF bexpr T_THEN block T_ELSE block
{ IF2 ($2,set_end_block (set_start_block $4 $3) $5,set_start_block $6 ($5+5)) }

| T_ID T_EQ iexpr                        { ASSIGN ($1,$3) }
| T_ASSERT bexpr                         { ASSERT $2 }

iexpr :
  T_ID                                      { VAR $1 }
| T_NUM                                     { CST $1 }
| T_RAND                                    { RAND }
| T_MINUS %prec T_UMINUS iexpr              { MINUS (CST 0.,$2) }
| iexpr T_PLUS  iexpr                       { PLUS ($1,$3) }
| iexpr T_MINUS iexpr                       { MINUS ($1,$3) }
| iexpr T_TIMES iexpr                       { TIMES ($1,$3) }
| T_LPAR iexpr T_RPAR                       { $2 }

block :
                         { (-1,[]) }
| inst                   { (-1,($1,-1)::[]) }
| T_BEGIN instlist T_END { set_end_block (set_start_block $2 $1) $3 }

instlist :
                            { (-1,[]) }
| inst                      { (-1,($1,-1)::[]) }
| inst T_SEMICOLON instlist { match $3 with (p,b) -> 
    (-1,(set_end_inst $1 $2,$2)::b) }


proglist:
  T_EOF                 { [] }
| T_SEMICOLON proglist  { $2 }
| T_PROG T_ID T_BEGINPROG instlist T_ENDPROG proglist 
    { ($2,set_end_block (set_start_block $4 $3) $5)::$6 }

