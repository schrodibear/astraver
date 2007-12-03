/**************************************************************************/
/*                                                                        */
/*  The Why/Caduceus/Krakatoa tool suite for program certification        */
/*  Copyright (C) 2002-2007                                               */
/*    Romain BARDOU                                                       */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Xavier URBAIN                                                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU General Public                   */
/*  License version 2, as published by the Free Software Foundation.      */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/*  See the GNU General Public License version 2 for more details         */
/*  (enclosed in the file GPL).                                           */
/*                                                                        */
/**************************************************************************/

/* $Id: jc_parser.mly,v 1.73 2007-12-03 15:33:35 marche Exp $ */

%{

  open Format
  open Jc_env
  open Jc_ast
  open Jc_pervasives
  open Parsing
  open Error

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)

  let locate_type e =
    { jc_ptype_node = e ; jc_ptype_loc = loc () }

  let locate_expr e =
    { jc_pexpr_node = e ; jc_pexpr_loc = loc () }

  let locate_tag e =
    { jc_ptag_node = e ; jc_ptag_loc = loc () }

  let locate_statement s =
    { jc_pstatement_node = s ; jc_pstatement_loc = loc () }

  let locate_decl d =
    { jc_pdecl_node = d ; jc_pdecl_loc = loc () }

  let skip = locate_statement JCPSskip
      

%}

%token <string> IDENTIFIER
%token <Jc_ast.const> CONSTANT
%token <string> STRING_LITERAL 
%token NULL

/* ( ) () { } [ ] .. */
%token LPAR RPAR LPARRPAR LBRACE RBRACE LSQUARE RSQUARE DOTDOT

/* ; , : . ? */
%token SEMICOLON COMMA COLON DOT QUESTION

/* - -- + ++ * / % */
%token MINUS MINUSMINUS PLUS PLUSPLUS STAR SLASH PERCENT
 
/* = <= >= > < == != <: :> */
%token EQ LTEQ GTEQ GT LT EQEQ BANGEQ LTCOLON COLONGT

/* += -= *= /= %= */
%token PLUSEQ MINUSEQ STAREQ SLASHEQ PERCENTEQ

/* && || => <=> ! */
%token AMPAMP BARBAR EQEQGT LTEQEQGT EXCLAM

/* if else return while break for fo break continue case switch default goto */
%token IF ELSE RETURN WHILE FOR DO BREAK CONTINUE CASE SWITCH DEFAULT GOTO

/* exception of throw try catch finally new free let in */
%token EXCEPTION OF THROW TRY CATCH FINALLY NEW FREE LET IN

/* pack unpack assert */
%token PACK UNPACK ASSERT

/* type invariant logic with variant and axiom */
%token TYPE INVARIANT LOGIC WITH VARIANT AND AXIOM

/* integer boolean real unit void rep */
%token INTEGER BOOLEAN REAL UNIT REP

/* assigns assumes behavior ensures requires throws reads */
%token ASSIGNS ASSUMES BEHAVIOR ENSURES REQUIRES THROWS READS

/* \forall \exists \offset_max \offset_min \old \result \mutable \typeof \bottom \typeeq */
%token BSFORALL BSEXISTS BSOFFSET_MAX BSOFFSET_MIN BSOLD BSRESULT BSMUTABLE BSTYPEOF BSBOTTOM BSTYPEEQ

/* \nothing */
%token BSNOTHING


/* & ~ ^ | << >> >>> */
%token AMP TILDE HAT PIPE LSHIFT LRSHIFT ARSHIFT

/* |= &= ^= */
%token BAREQ AMPEQ CARETEQ

/*
%token FLOAT DOUBLE 
*/

%token EOF
%type <Jc_ast.pdecl list> file
%start file

/* precedences on statements (from lowest to highest) */

%nonassoc PRECIF
%nonassoc ELSE

%nonassoc PRECTRY
%nonassoc FINALLY

%nonassoc PRECLOGIC
%nonassoc EQ

%nonassoc PRECTYPE
/* and */
%right AND

/* precedences on expressions  */

%nonassoc COLON
%nonassoc PRECFORALL 
/* <=> */
%right LTEQEQGT
/* => */
%right EQEQGT 
%left QUESTION ASSIGNOP
%left BARBAR
%left AMPAMP
%left PIPE
%left HAT
%left AMP
%left LT GT LTEQ GTEQ EQEQ BANGEQ COLONGT LTCOLON
%nonassoc DOTDOT
/* unary -, unary +, ++, --, ! ~ */
%nonassoc UMINUS UPLUS PLUSPLUS MINUSMINUS EXCLAM TILDE
/* . */
%nonassoc DOT



%%

/****************************************/
/* a file is a sequence of declarations */
/****************************************/

file: 
| decl file 
    { $1::$2 }
| rec_decls file 
    { $1::$2 }
| EOF 
    { [] }
;

rec_decls:
| type_rec_definitions %prec PRECTYPE
    { locate_decl (JCPDrectypes($1)) }
| function_rec_definitions %prec PRECTYPE
    { locate_decl (JCPDrecfuns($1)) }
| logic_rec_definitions %prec PRECTYPE
    { locate_decl (JCPDrecfuns($1)) }

decl: 
| variable_definition
    { $1 }
| function_definition 
    { $1 }
| type_definition 
    { $1 }
| axiom_definition
    { $1 }
| global_invariant_definition
    { $1 }
| exception_definition
    { $1 }
| logic_definition
    { $1 }
/*
| error
    { Jc_options.parsing_error (loc ()) "'type' or type expression expected" }
*/
;


/*******************/
/* type definition */	      
/*******************/

type_rec_definitions:
| type_definition AND type_rec_definitions %prec PRECTYPE
    { $1::$3 }
| type_definition AND type_definition %prec PRECTYPE
    { $1::[$3] }

type_definition:
| TYPE IDENTIFIER EQ int_constant DOTDOT int_constant
    { locate_decl (JCPDenumtype($2,$4,$6)) }
| TYPE IDENTIFIER EQ extends LBRACE field_declaration_list RBRACE
    { let (f,i) = $6 in locate_decl (JCPDstructtype($2,$4,f,i)) }
| LOGIC TYPE IDENTIFIER
    { locate_decl (JCPDlogictype($3)) }
; 

int_constant:
| CONSTANT 
    { num_of_constant (loc_i 1)$1 }
| MINUS CONSTANT
    { Num.minus_num (num_of_constant (loc_i 2) $2) }
;

extends:
| /* epsilon */
    { None }
| IDENTIFIER WITH
    { Some $1 }
;

field_declaration_list:
| /* epsilon */
    { ([],[]) }
| field_declaration field_declaration_list
    { let (f,i) = $2 in ($1::f,i) }
| invariant field_declaration_list
    { let (f,i) = $2 in (f,$1::i) }
;

field_declaration:
| type_expr IDENTIFIER SEMICOLON
    { (false, $1, $2) }
| REP type_expr IDENTIFIER SEMICOLON
    { (true, $2, $3) }
;

invariant:
| INVARIANT IDENTIFIER LPAR IDENTIFIER RPAR EQ expression SEMICOLON
    { ($2,$4,$7) }
;



/***********************/
/* Function definition */
/***********************/


parameters:
| LPARRPAR
    { [] }
| LPAR RPAR
    { [] }
| LPAR parameter_comma_list RPAR
    { $2 } 
;

parameter_comma_list: 
| parameter_declaration 
    { [$1] }
| parameter_declaration COMMA parameter_comma_list 
    { $1 :: $3 }
;

parameter_declaration:
| type_expr IDENTIFIER
    { ($1,$2) }
;


type_expr:
| INTEGER
    { locate_type (JCPTnative Tinteger) }
| BOOLEAN
    { locate_type (JCPTnative Tboolean) }
| REAL
    { locate_type (JCPTnative Treal) }
| UNIT
    { locate_type (JCPTnative Tunit) }
| IDENTIFIER
    { locate_type (JCPTidentifier $1) }
| IDENTIFIER LSQUARE DOTDOT RSQUARE
    { locate_type (JCPTpointer($1,None,None)) }
| IDENTIFIER LSQUARE CONSTANT RSQUARE
    { let n = num_of_constant (loc_i 3) $3 in
      locate_type (JCPTpointer($1,Some n,Some n)) }
| IDENTIFIER LSQUARE CONSTANT DOTDOT RSQUARE
    { let n = num_of_constant (loc_i 3) $3 in
      locate_type (JCPTpointer($1,Some n,None)) }
| IDENTIFIER LSQUARE CONSTANT DOTDOT CONSTANT RSQUARE
    { let n = num_of_constant (loc_i 3) $3 in
      let m = num_of_constant (loc_i 5) $5 in
      locate_type (JCPTpointer($1,Some n,Some m)) }
| IDENTIFIER LSQUARE DOTDOT CONSTANT RSQUARE
    { let m = num_of_constant (loc_i 4) $4 in
      locate_type (JCPTpointer($1,None,Some m)) }
;

function_specification:
| /* epsilon */ 
    { [] }
| spec_clause function_specification 
    { $1::$2 }
;

spec_clause:
| REQUIRES expression SEMICOLON
    { JCPCrequires($2) }
/*
| ENSURES expression SEMICOLON
    { JCPCensures($2) }
*/
| BEHAVIOR ident_or_default COLON throws assumes requires assigns 
  ENSURES expression SEMICOLON
    { JCPCbehavior(loc_i 2,$2,$4,$5,$6,$7,$9) }
;

ident_or_default:
| IDENTIFIER { $1 }
| DEFAULT { "default" }

throws:
| /* epsilon */
    { None }
| THROWS identifier SEMICOLON
    { Some $2 }
;

assumes:
| /* epsilon */
    { None }
| ASSUMES expression SEMICOLON
    { Some $2 }
;

requires:
| /* epsilon */
    { None }
| REQUIRES expression SEMICOLON
    { Some $2 }
;

assigns:
| /* epsilon */
    { None }
| ASSIGNS argument_expression_list SEMICOLON
    { Some(loc_i 2,$2) }
| ASSIGNS BSNOTHING SEMICOLON
    { Some (loc_i 2,[]) }
;

reads:
| /* epsilon */
    { [] }
| READS argument_expression_list SEMICOLON
    { $2 }
| READS BSNOTHING SEMICOLON
    { [] }
;

function_rec_definitions:
| function_definition AND function_rec_definitions %prec PRECTYPE
    { $1::$3 }
| function_definition AND function_definition %prec PRECTYPE
    { $1::[$3] }

function_definition: 
| type_expr identifier parameters function_specification compound_statement
    { locate_decl (JCPDfun($1, $2, $3, $4, Some $5)) }
| type_expr identifier parameters function_specification SEMICOLON
    { locate_decl (JCPDfun($1, $2, $3, $4, None)) }
;


/******************************/
/* Global variable definition */
/******************************/

variable_definition:
| type_expr IDENTIFIER EQ expression SEMICOLON
    { locate_decl (JCPDvar($1,$2,Some $4)) }
| type_expr IDENTIFIER SEMICOLON
    { locate_decl (JCPDvar($1,$2,None)) }
;

/***************/
/* axioms */
/**********/

axiom_definition:
| AXIOM IDENTIFIER COLON expression
    { locate_decl( JCPDaxiom($2,$4)) }
;


/********************/
/* global invariant */
/********************/

global_invariant_definition:
| INVARIANT IDENTIFIER COLON expression
    { locate_decl( JCPDglobinv($2,$4)) }
;


/*************************/
/* exception definitions */
/*************************/

exception_definition:
| EXCEPTION IDENTIFIER OF type_expr
    { locate_decl (JCPDexception($2,$4)) }
;


/***************/
/* expressions */
/***************/

primary_expression: 
| IDENTIFIER 
    { locate_expr (JCPEvar $1) }
| BSRESULT
    { locate_expr (JCPEvar "\\result") }
| CONSTANT 
    { locate_expr (JCPEconst $1) }
| LPARRPAR 
    { locate_expr (JCPEconst JCCvoid) }
| NULL 
    { locate_expr (JCPEconst JCCnull) }
/*
| STRING_LITERAL 
    { locate (CEstring_literal $1) }
*/
| LPAR expression RPAR 
    { $2 }
| LPAR IDENTIFIER COLON expression RPAR
    { locate_expr (JCPElabel($2,$4)) }
;

postfix_expression: 
| primary_expression 
    { $1 }
| primary_expression LPAR argument_expression_list_opt RPAR 
    { locate_expr (JCPEapp($1, $3)) }
| primary_expression LPARRPAR 
    { locate_expr (JCPEapp($1, [])) }
| BSOLD LPAR expression RPAR 
    { locate_expr (JCPEold($3)) }
| BSOFFSET_MAX LPAR expression RPAR 
    { locate_expr (JCPEoffset(Offset_max,$3)) }
| BSOFFSET_MIN LPAR expression RPAR 
    { locate_expr (JCPEoffset(Offset_min,$3)) }
| postfix_expression DOT IDENTIFIER
    { locate_expr (JCPEderef ($1, $3)) }
| postfix_expression PLUSPLUS 
    { locate_expr (JCPEunary (UPpostfix_inc, $1)) }
| postfix_expression MINUSMINUS
    { locate_expr (JCPEunary (UPpostfix_dec, $1)) }
| PLUSPLUS postfix_expression 
    { locate_expr (JCPEunary (UPprefix_inc, $2)) }
| MINUSMINUS postfix_expression 
    { locate_expr (JCPEunary (UPprefix_dec, $2)) }
| PLUS postfix_expression %prec UPLUS
    { locate_expr (JCPEunary (UPplus, $2)) }
| MINUS postfix_expression %prec UMINUS
    { locate_expr (JCPEunary (UPminus, $2)) }
| TILDE postfix_expression 
    { locate_expr (JCPEunary (UPbw_not, $2)) }
| EXCLAM postfix_expression 
    { locate_expr (JCPEunary (UPnot, $2)) }
| LSQUARE expression DOTDOT expression RSQUARE
    { locate_expr (JCPErange(Some $2,Some $4)) }
| LSQUARE DOTDOT expression RSQUARE 
    { locate_expr (JCPErange(None,Some $3)) }
| LSQUARE expression DOTDOT RSQUARE 
    { locate_expr (JCPErange(Some $2,None)) }
| LSQUARE DOTDOT RSQUARE 
    { locate_expr (JCPErange(None,None)) }
;

argument_expression_list: 
| expression 
    { [$1] }
| expression COMMA argument_expression_list 
    { $1::$3 }
;

argument_expression_list_opt: 
| /* $\varepsilon$ */
    { [] }
| argument_expression_list 
    { $1 }
;


multiplicative_expression: 
| postfix_expression 
    { $1 }
| multiplicative_expression STAR postfix_expression 
    { locate_expr (JCPEbinary ($1, BPmul, $3)) }
| multiplicative_expression SLASH postfix_expression 
    { locate_expr (JCPEbinary ($1, BPdiv, $3)) }
| multiplicative_expression PERCENT postfix_expression 
    { locate_expr (JCPEbinary ($1, BPmod, $3)) }
;

additive_expression: 
| multiplicative_expression 
    { $1 }
| additive_expression PLUS multiplicative_expression 
    { locate_expr (JCPEbinary ($1, BPadd, $3)) }
| additive_expression MINUS multiplicative_expression 
    { locate_expr (JCPEbinary ($1, BPsub, $3)) }
;

shift_expression: 
| additive_expression 
    { $1 }
| shift_expression LSHIFT additive_expression 
    { locate_expr (JCPEbinary ($1, BPshift_left, $3)) }
| shift_expression LRSHIFT additive_expression 
    { locate_expr (JCPEbinary ($1, BPlogical_shift_right, $3)) }
| shift_expression ARSHIFT additive_expression 
    { locate_expr (JCPEbinary ($1, BParith_shift_right, $3)) }
;

assignment_operator: 
| EQ { `Aeq }
| PLUSEQ { `Aadd }
| MINUSEQ { `Asub }
| STAREQ { `Amul }
| SLASHEQ { `Adiv }
| PERCENTEQ { `Amod }
/*
| LEFT_ASSIGN { Aleft }
| RIGHT_ASSIGN { Aright }
*/
| AMPEQ { `Aand }
| CARETEQ { `Axor }
| BAREQ { `Aor }
;


expression: 
| shift_expression 
    { $1 }
| NEW IDENTIFIER LSQUARE expression RSQUARE
    { locate_expr (JCPEalloc ($4, $2)) }
| FREE LPAR expression RPAR
    { locate_expr (JCPEfree $3) }
| expression LT expression 
    { locate_expr (JCPEbinary ($1, BPlt, $3)) }
| expression GT expression
    { locate_expr (JCPEbinary ($1, BPgt, $3)) }
| expression LTEQ expression
    { locate_expr (JCPEbinary ($1, BPle, $3)) }
| expression GTEQ expression
    { locate_expr (JCPEbinary ($1, BPge, $3)) }
| expression LTCOLON IDENTIFIER
    { locate_expr (JCPEinstanceof($1, $3)) }
| expression COLONGT IDENTIFIER
    { locate_expr (JCPEcast($1, $3)) }
| expression EQEQ expression 
    { locate_expr (JCPEbinary ($1, BPeq, $3)) }
| expression BANGEQ expression 
    { locate_expr (JCPEbinary ($1, BPneq, $3)) }
| expression AMP expression 
    { locate_expr (JCPEbinary ($1, BPbw_and, $3)) }
| expression HAT expression 
    { locate_expr (JCPEbinary ($1, BPbw_xor, $3)) }
| expression PIPE expression 
    { locate_expr (JCPEbinary ($1, BPbw_or, $3)) }
| expression AMPAMP expression 
    { locate_expr (JCPEbinary($1, BPland, $3)) }
| expression BARBAR expression 
    { locate_expr (JCPEbinary($1, BPlor, $3)) }
| expression QUESTION expression COLON expression %prec QUESTION
    { locate_expr (JCPEif ($1, $3, $5)) }
| LET IDENTIFIER EQ expression IN expression %prec PRECFORALL
    { locate_expr (JCPElet ($2, $4, $6)) }
| postfix_expression assignment_operator expression %prec ASSIGNOP
    { let a  =
	match $2 with
		| `Aeq -> JCPEassign ($1, $3)
		| `Aadd -> JCPEassign_op ($1, BPadd, $3)
		| `Asub -> JCPEassign_op ($1, BPsub, $3)
		| `Amul -> JCPEassign_op ($1, BPmul, $3)
		| `Adiv -> JCPEassign_op ($1, BPdiv, $3)
		| `Amod -> JCPEassign_op ($1, BPmod, $3)
		| `Aand -> JCPEassign_op ($1, BPbw_and, $3)
		| `Axor -> JCPEassign_op ($1, BPbw_xor, $3)
		| `Aor -> JCPEassign_op ($1, BPbw_or, $3)
(*
		| Aleft -> CEassign_op ($1, BPshift_left, $3)
		| Aright -> CEassign_op ($1, BPshift_right, $3)
*)
      in locate_expr a }

| BSFORALL type_expr identifier_list SEMICOLON expression 
    %prec PRECFORALL
    { locate_expr (JCPEquantifier(Forall,$2,$3,$5)) }
| BSEXISTS type_expr identifier_list SEMICOLON expression 
    %prec PRECFORALL
    { locate_expr (JCPEquantifier(Exists,$2,$3,$5)) }
| expression EQEQGT expression
    { locate_expr (JCPEbinary($1,BPimplies,$3)) }
| expression LTEQEQGT expression
    { locate_expr (JCPEbinary($1,BPiff,$3)) }
/*
| expression COMMA assignment_expression { locate (CEseq ($1, $3)) }
*/
| BSMUTABLE LPAR expression COMMA tag RPAR
    { locate_expr (JCPEmutable($3, $5)) }
| BSMUTABLE LPAR expression RPAR
    { locate_expr (JCPEmutable($3, locate_tag JCPTbottom)) }
| BSTYPEEQ LPAR tag COMMA tag RPAR
    { locate_expr (JCPEtagequality($3, $5)) }
;

expression_opt: 
| /* $\varepsilon$ */
    { None }
| expression
    { Some $1 }
;

tag:
| identifier
    { locate_tag (JCPTtag $1) }
| BSBOTTOM
    { locate_tag JCPTbottom }
| BSTYPEOF LPAR expression RPAR
    { locate_tag (JCPTtypeof $3) }
;

identifier_list: 
| IDENTIFIER 
    { [$1] }
| IDENTIFIER COMMA identifier_list 
    { $1 :: $3 }
;

identifier:
| IDENTIFIER
    { { jc_identifier_loc = loc () ; jc_identifier_name = $1 } }
;

/****************/
/* declarations */
/****************/


declaration: 
| type_expr IDENTIFIER SEMICOLON 
    { locate_statement (JCPSdecl($1,$2,None)) }
| type_expr IDENTIFIER EQ expression SEMICOLON 
    { locate_statement (JCPSdecl($1,$2,Some $4)) }
;


/**************/
/* statements */
/**************/

labeled_statement:
| identifier COLON statement 
    { locate_statement (JCPSlabel($1.jc_identifier_name,$3)) }
;

/*
case_statement:
| CASE CONSTANT COLON statement_list 
    { Case $2, $4 }
;

default_statement:
| DEFAULT COLON statement_list
    { Default, $3 }
;

case_statement_list: 
|  
    { [] }
| case_statement case_statement_list 
    { $1 :: $2 }
;

default_case_statement_list:
| case_statement_list default_statement
    { $1 @ [$2] }
| case_statement_list
    { $1 }
;
*/

compound_statement:
| LBRACE statement_list RBRACE 
	    { $2 }
;

statement_list: 
| /* epsilon */ 
    { [] }
| statement statement_list 
    { $1 :: $2 }
;


expression_statement: 
| SEMICOLON 
    { skip }
/*
| CODE_ANNOT { locate (CSannot $1) } 
*/
| expression SEMICOLON 
    { locate_statement (JCPSexpr $1) }
| ASSERT expression SEMICOLON
    { locate_statement (JCPSassert((*None,*)$2)) }
/*
| ASSERT identifier COLON expression SEMICOLON
    { locate_statement (JCPSassert(Some $2,$4)) }
*/
;

selection_statement: 
| IF LPAR expression RPAR statement 
    %prec PRECIF 
    { locate_statement (JCPSif($3, $5, skip)) }
| IF LPAR expression RPAR statement ELSE statement 
    { locate_statement (JCPSif ($3, $5, $7)) }
| SWITCH LPAR expression RPAR LBRACE switch_block RBRACE
    { locate_statement (JCPSswitch ($3, $6)) }
;

switch_block: 
| /* $\varepsilon$ */
    { [] }
| switch_labels 
    { [($1,[])] }
| switch_labels statement statement_list switch_block
    { ($1,$2::$3)::$4 }
;

switch_labels:
| switch_label
    { [$1] }
| switch_label switch_labels
    { $1::$2 }
;

switch_label:
| CASE expression COLON
    { Some($2) }
| DEFAULT COLON
    { None }
;

iteration_statement: 
| WHILE expression loop_annot_opt statement 
    { let (i,v) = $3 in 
      locate_statement (JCPSwhile ($2, i, v, $4)) }
/*
| loop_annot DO statement WHILE LPAR expression RPAR SEMICOLON 
    { locate (CSdowhile ($1, $3, $6)) }
*/
| FOR LPAR argument_expression_list_opt SEMICOLON expression SEMICOLON 
    argument_expression_list_opt RPAR loop_annot_opt statement
    { let (i,v) = $9 in 
      locate_statement (JCPSfor($3, $5, $7, i, v, $10)) }
;

loop_annot_opt:
| INVARIANT expression SEMICOLON VARIANT expression SEMICOLON
    { ($2, Some $5) }
| INVARIANT expression SEMICOLON
    { ($2, None) }
| VARIANT expression SEMICOLON
    { (locate_expr (JCPEconst(JCCboolean true)), Some $2) }
| SEMICOLON
    { (locate_expr (JCPEconst(JCCboolean true)), None) }
;

jump_statement: 
| GOTO identifier SEMICOLON 
    { locate_statement (JCPSgoto $2.jc_identifier_name) }
/*
| CONTINUE SEMICOLON { locate CScontinue }
*/
| BREAK SEMICOLON 
    { locate_statement (JCPSbreak "") }
| RETURN SEMICOLON { locate_statement (JCPSreturn None) }
| RETURN expression SEMICOLON 
    { locate_statement (JCPSreturn (Some $2)) }
;

pack_statement:
| PACK LPAR expression COMMA identifier RPAR SEMICOLON
    { locate_statement (JCPSpack ($3, Some $5)) }
| PACK LPAR expression RPAR SEMICOLON
    { locate_statement (JCPSpack ($3, None)) }
| UNPACK LPAR expression COMMA identifier RPAR SEMICOLON
    { locate_statement (JCPSunpack ($3, Some $5)) }
| UNPACK LPAR expression RPAR SEMICOLON
    { locate_statement (JCPSunpack ($3, None)) }
;

statement: 
| labeled_statement 
    { $1 }
| compound_statement 
    { locate_statement (JCPSblock $1) }
| expression_statement 
    { $1 }
| selection_statement 
    { $1 }
| iteration_statement 
    { $1 }
| jump_statement 
    { $1 }
| declaration
    { $1 }
/*
| SPEC statement { locate (CSspec ($1,$2)) }
*/
| pack_statement { $1 }
| exception_statement { $1 }
;


catch_statement: 
| CATCH identifier IDENTIFIER statement
    { ($2, $3, $4) }
;

catch_statement_list:
| /* epsilon */ 
    { [] }
| catch_statement catch_statement_list 
    { $1 :: $2 }
;

exception_statement:
| THROW identifier expression_opt SEMICOLON
   { locate_statement (JCPSthrow($2,$3)) }
| TRY statement catch_statement_list %prec PRECTRY
   { locate_statement (JCPStry($2, $3, skip)) }
| TRY statement catch_statement_list FINALLY statement
   { locate_statement (JCPStry($2, $3, $5)) }
;

/**********************************/
/* Logic functions and predicates */
/**********************************/

logic_definition:
/* constants def */
| LOGIC type_expr IDENTIFIER EQ expression
    { locate_decl (JCPDlogic(Some $2, $3, [], JCPExpr $5)) }
/* constants no def */
| LOGIC type_expr IDENTIFIER 
    { locate_decl (JCPDlogic(Some $2, $3, [], JCPReads [])) }
/* logic fun def */
| LOGIC type_expr IDENTIFIER parameters EQ expression
    { locate_decl (JCPDlogic(Some $2, $3, $4, JCPExpr $6)) }
/* logic pred def */
| LOGIC IDENTIFIER parameters EQ expression
    { locate_decl (JCPDlogic(None, $2, $3, JCPExpr $5)) }
/* logic fun reads */
| LOGIC type_expr IDENTIFIER parameters reads %prec PRECLOGIC
    { locate_decl (JCPDlogic(Some $2, $3, $4, JCPReads $5)) }
/* logic pred reads */
| LOGIC IDENTIFIER parameters reads %prec PRECLOGIC
    { locate_decl (JCPDlogic(None, $2, $3, JCPReads $4)) }
;

logic_rec_definitions:
| logic_definition AND logic_rec_definitions %prec PRECTYPE
    { $1::$3 }
| logic_definition AND logic_definition %prec PRECTYPE
    { $1::[$3] }


/*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*/
