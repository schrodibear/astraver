/**************************************************************************/
/*                                                                        */
/*  The Why/Caduceus/Krakatoa tool suite for program certification        */
/*  Copyright (C) 2002-2006                                               */
/*    Jean-François COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLIÂTRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCHÉ                                                       */
/*    Yannick MOY                                                         */
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

/* $Id: jc_parser.mly,v 1.32 2007-04-04 12:45:07 marche Exp $ */

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

  let locate_statement s =
    { jc_pstatement_node = s ; jc_pstatement_loc = loc () }

  let locate_decl d =
    { jc_pdecl_node = d ; jc_pdecl_loc = loc () }


(*
  let locate x = { node = x; loc = loc() }
  let locate_i i x = { node = x; loc = loc_i i }
  let with_loc l x = { node = x; loc = l }
*)

  let skip = locate_statement JCPSskip
      

%}

%token <string> IDENTIFIER
%token <Jc_ast.const> CONSTANT
%token <string> STRING_LITERAL 

/* ( ) { } [ ] .. */
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
%token AMPAMP BARBAR EQGT LTEQGT EXCLAM

/* if else return while break */
%token IF ELSE RETURN WHILE BREAK  

/* exception of throw try catch */
%token EXCEPTION OF THROW TRY CATCH

/* pack unpack assert */
%token PACK UNPACK ASSERT

/* type invariant logic with variant and */
%token TYPE INVARIANT LOGIC WITH VARIANT AND

/* integer boolean real unit */
%token INTEGER BOOLEAN REAL UNIT

/* assigns assumes behavior ensures requires throws */
%token ASSIGNS ASSUMES BEHAVIOR ENSURES REQUIRES THROWS

/* \forall \offset_max \offset_min \old \result  */
%token BSFORALL BSOFFSET_MAX BSOFFSET_MIN BSOLD BSRESULT 

/* \nothing */
%token BSNOTHING

/* axiom */
%token AXIOM

/*

%token LEFT_OP RIGHT_OP 
%token OR_OP MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN 
%token LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN
%token XOR_ASSIGN OR_ASSIGN

%token CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE VOID
%token STRUCT ENUM 

%token CASE DEFAULT SWITCH DO FOR GOTO CONTINUE 
%token TRY CATCH FINALLY THROW 

%token AMP EXL TILDE STAR SLASH PERCENT LT GT HAT PIPE
%token QUESTION

*/

%token EOF
%type <Jc_ast.pdecl list> file
%start file

/* precedences on statements (from lowest to highest) */

%nonassoc PRECIF
%nonassoc ELSE

%nonassoc PRECTYPE
/* and */
%right AND

/* precedences on expressions  */

%nonassoc PRECFORALL
/* <=> */
%right LTEQGT
/* => */
%right EQGT 
%left QUESTION ASSIGNOP
%left BARBAR
%left AMPAMP
%left LT GT LTEQ GTEQ EQEQ BANGEQ COLONGT LTCOLON
/* unary -, unary +, ++, --, ! */
%nonassoc UMINUS UPLUS PLUSPLUS MINUSMINUS EXCLAM
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

decl: 
| function_definition 
    { $1 }
| type_definition 
    { $1 }
| axiom_definition
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
    { locate_decl (JCPDrangetype($2,$4,$6)) }
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
    { ($1,$2) }
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
    { locate_type (JCPTpointer($1,zero,minus_one)) }
| IDENTIFIER LSQUARE CONSTANT RSQUARE
    { let n = num_of_constant (loc_i 3) $3 in
      locate_type (JCPTpointer($1,n,n)) }
| IDENTIFIER LSQUARE CONSTANT DOTDOT RSQUARE
    { let n = num_of_constant (loc_i 3) $3 in
      locate_type (JCPTpointer($1,n,Num.pred_num n)) }
| IDENTIFIER LSQUARE CONSTANT DOTDOT CONSTANT RSQUARE
    { let n = num_of_constant (loc_i 3) $3 in
      let m = num_of_constant (loc_i 5) $5 in
      locate_type (JCPTpointer($1,n,m)) }
| IDENTIFIER LSQUARE DOTDOT CONSTANT RSQUARE
    { let m = num_of_constant (loc_i 4) $4 in
      locate_type (JCPTpointer($1,Num.succ_num m,m)) }
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
| BEHAVIOR IDENTIFIER COLON throws assumes assigns ENSURES expression SEMICOLON
    { JCPCbehavior($2,$4,$5,$6,$8) }
	
;

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

assigns:
| /* epsilon */
    { None }
| ASSIGNS argument_expression_list SEMICOLON
    { Some $2 }
| ASSIGNS BSNOTHING SEMICOLON
    { Some [] }
;


function_definition: 
| type_expr IDENTIFIER parameters function_specification compound_statement
    { locate_decl (JCPDfun($1, $2, $3, $4, $5)) }
;

/***************/
/* axioms */
/**********/

axiom_definition:
| AXIOM IDENTIFIER COLON expression
    { locate_decl( JCPDaxiom($2,$4)) }
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
/*
| STRING_LITERAL 
    { locate (CEstring_literal $1) }
*/
| LPAR expression RPAR { $2 }
;

postfix_expression: 
| primary_expression 
    { $1 }
| primary_expression LPAR RPAR 
    { locate_expr (JCPEapp($1, [])) }
| primary_expression LPAR argument_expression_list RPAR 
    { locate_expr (JCPEapp($1, $3)) }
| BSOLD LPAR expression RPAR 
    { locate_expr (JCPEold($3)) }
| BSOFFSET_MAX LPAR expression RPAR 
    { locate_expr (JCPEoffset_max($3)) }
| BSOFFSET_MIN LPAR expression RPAR 
    { locate_expr (JCPEoffset_min($3)) }
| postfix_expression DOT IDENTIFIER
    { locate_expr (JCPEderef ($1, $3)) }
| postfix_expression PLUSPLUS 
    { locate_expr (JCPEunary (Upostfix_inc, $1)) }
| postfix_expression MINUSMINUS
    { locate_expr (JCPEunary (Upostfix_dec, $1)) }
| PLUSPLUS postfix_expression 
    { locate_expr (JCPEunary (Uprefix_inc, $2)) }
| MINUSMINUS postfix_expression 
    { locate_expr (JCPEunary (Uprefix_dec, $2)) }
| PLUS postfix_expression %prec UPLUS
    { locate_expr (JCPEunary (Uplus, $2)) }
| MINUS postfix_expression %prec UMINUS
    { locate_expr (JCPEunary (Uminus, $2)) }
/*
| TILDE postfix_expression 
    { locate_expr (JCPEunary (Utilde, $2)) }
*/
| EXCLAM postfix_expression 
    { locate_expr (JCPEunary (Unot, $2)) }
;

argument_expression_list: 
| expression 
    { [$1] }
| expression COMMA argument_expression_list 
    { $1::$3 }
;


multiplicative_expression: 
| postfix_expression 
    { $1 }
| multiplicative_expression STAR postfix_expression 
    { locate_expr (JCPEbinary ($1, Bmul, $3)) }
| multiplicative_expression SLASH postfix_expression 
    { locate_expr (JCPEbinary ($1, Bdiv, $3)) }
| multiplicative_expression PERCENT postfix_expression 
    { locate_expr (JCPEbinary ($1, Bmod, $3)) }
;

additive_expression: 
| multiplicative_expression 
    { $1 }
| additive_expression PLUS multiplicative_expression 
    { locate_expr (JCPEbinary ($1, Badd, $3)) }
| additive_expression MINUS multiplicative_expression 
    { locate_expr (JCPEbinary ($1, Bsub, $3)) }
;

shift_expression: 
| additive_expression 
    { $1 }
/*
| shift_expression LEFT_OP additive_expression 
    { locate (CEbinary ($1, Bshift_left, $3)) }
| shift_expression RIGHT_OP additive_expression 
    { locate (CEbinary ($1, Bshift_right, $3)) }
*/
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
| AND_ASSIGN { Aand }
| XOR_ASSIGN { Axor }
| OR_ASSIGN { Aor }
*/
;


expression: 
| shift_expression 
    { $1 }
| expression LT expression 
    { locate_expr (JCPEbinary ($1, Blt, $3)) }
| expression GT expression
    { locate_expr (JCPEbinary ($1, Bgt, $3)) }
| expression LTEQ expression
    { locate_expr (JCPEbinary ($1, Ble, $3)) }
| expression GTEQ expression
    { locate_expr (JCPEbinary ($1, Bge, $3)) }
| expression LTCOLON IDENTIFIER
    { locate_expr (JCPEinstanceof($1, $3)) }
| expression COLONGT IDENTIFIER
    { locate_expr (JCPEcast($1, $3)) }
| expression EQEQ expression 
    { locate_expr (JCPEbinary ($1, Beq, $3)) }
| expression BANGEQ expression 
    { locate_expr (JCPEbinary ($1, Bneq, $3)) }
/*
| _expression AMP expression 
    { locate (CEbinary ($1, Bbw_and, $3)) }
*/
/*
| expression HAT expression 
    { locate (CEbinary ($1, Bbw_xor, $3)) }
*/
/*
| expression PIPE expression 
    { locate (CEbinary ($1, Bbw_or, $3)) }
*/
| expression AMPAMP expression 
    { locate_expr (JCPEbinary($1, Bland, $3)) }
| expression BARBAR expression 
    { locate_expr (JCPEbinary($1, Blor, $3)) }
| expression QUESTION expression COLON expression %prec QUESTION
    { locate_expr (JCPEif ($1, $3, $5)) }
| postfix_expression assignment_operator expression %prec ASSIGNOP
    { let a  =
	match $2 with
		| `Aeq -> JCPEassign ($1, $3)
		| `Aadd -> JCPEassign_op ($1, Badd, $3)
		| `Asub -> JCPEassign_op ($1, Bsub, $3)
		| `Amul -> JCPEassign_op ($1, Bmul, $3)
		| `Adiv -> JCPEassign_op ($1, Bdiv, $3)
		| `Amod -> JCPEassign_op ($1, Bmod, $3)
(*
		| Aleft -> CEassign_op ($1, Bshift_left, $3)
		| Aright -> CEassign_op ($1, Bshift_right, $3)
		| Aand -> CEassign_op ($1, Bbw_and, $3)
		| Axor -> CEassign_op ($1, Bbw_xor, $3)
		| Aor -> CEassign_op ($1, Bbw_or, $3)
*)
      in locate_expr a }

| BSFORALL type_expr identifier_list SEMICOLON expression 
    %prec PRECFORALL
    { locate_expr (JCPEforall($2,$3,$5)) }
| expression EQGT expression
    { locate_expr (JCPEbinary($1,Bimplies,$3)) }
| expression LTEQGT expression
    { locate_expr (JCPEbinary($1,Biff,$3)) }
/*
| expression COMMA assignment_expression { locate (CEseq ($1, $3)) }
*/
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

/*

labeled_statement
        : identifier COLON statement { locate (CSlabel ($1, $3)) }
        | CASE constant_expression COLON statement { locate (CScase ($2, $4)) }
        | DEFAULT COLON statement { locate (CSdefault($3)) }
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
    { locate_statement (JCPSassert $2) }
;

selection_statement: 
| IF LPAR expression RPAR statement 
    %prec PRECIF 
    { locate_statement (JCPSif($3, $5, skip)) }
| IF LPAR expression RPAR statement ELSE statement 
    { locate_statement (JCPSif ($3, $5, $7)) }
/*
| SWITCH LPAR expression RPAR statement 
    { locate (CSswitch ($3, $5)) }
*/
;

iteration_statement: 
| WHILE expression loop_annot statement 
    { let (i,v) = $3 in 
      locate_statement (JCPSwhile ($2, i, v, $4)) }
/*
| loop_annot DO statement WHILE LPAR expression RPAR SEMICOLON 
    { locate (CSdowhile ($1, $3, $6)) }
| loop_annot FOR LPAR expression_statement expression_statement RPAR 
        statement
	{ locate (CSfor ($1, expr_of_statement $4, expr_of_statement $5, 
			 locate CEnop, $7)) }
| loop_annot 
            FOR LPAR expression_statement expression_statement expression RPAR 
            statement 
	    { locate (CSfor ($1, expr_of_statement $4, expr_of_statement $5, 
			     $6, $8)) }
        ;
*/
;

loop_annot:
| INVARIANT expression SEMICOLON VARIANT expression SEMICOLON
    { ($2,$5) }
;

jump_statement: 
/*
| GOTO identifier SEMICOLON { locate (CSgoto $2) }
| CONTINUE SEMICOLON { locate CScontinue }
*/
| BREAK SEMICOLON { locate_statement (JCPSbreak "") }
/*
| RETURN SEMICOLON { locate (CSreturn None) }
*/
| RETURN expression SEMICOLON { locate_statement (JCPSreturn $2) }
;

pack_statement:
| PACK LPAR expression RPAR SEMICOLON
    { locate_statement (JCPSpack $3 ) }
| UNPACK LPAR expression RPAR SEMICOLON
    { locate_statement (JCPSunpack $3 ) }
;

statement: 
/*
| labeled_statement 
    { $1 }
*/
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


exception_statement:
| THROW identifier expression SEMICOLON
   { locate_statement (JCPSthrow($2,Some $3)) }
| TRY statement CATCH identifier IDENTIFIER statement
   { locate_statement (JCPStry($2,[($4,$5,$6)],skip)) }
;

/**********************************/
/* Logic functions and predicates */
/**********************************/

logic_definition:
| LOGIC type_expr IDENTIFIER parameters EQ expression
    { locate_decl (JCPDlogic(Some $2, $3, $4, $6)) }
| LOGIC IDENTIFIER parameters EQ expression
    { locate_decl (JCPDlogic(None, $2, $3, $5)) }
;

/*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*/
