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

/* $Id: jc_parser.mly,v 1.140 2010-02-11 08:05:24 marche Exp $ */

%{

  open Format
  open Jc_env
  open Jc_ast
  open Jc_pervasives
  open Parsing
  open Error
  open Jc_constructors

  let pos () = (symbol_start_pos (), symbol_end_pos ())
  let pos_i i = (rhs_start_pos i, rhs_end_pos i)

  let locate n = new node_positioned ~pos:(pos ()) n
  let locate_identifier n = new identifier ~pos:(pos ()) n

  let skip = locate (JCPEconst JCCvoid)

  let label s = match s with
    | "Pre" -> LabelPre
    | "Old" -> LabelOld
    | "Here" -> LabelHere
    | "Post" -> LabelPost
    | _ -> 
	LabelName { 
	  label_info_name = s; 
	  label_info_final_name = s;
	  times_used = 0;
	}

  let lparams =
    List.map
      (fun (v,t,x) ->
	 if v then (t,x) else
	   Jc_options.parsing_error
	     Loc.dummy_position
	     "logic params cannot not be in invalid state")
%}

%token <string> IDENTIFIER
%token <Jc_ast.const> CONSTANT
%token <string> STRING_LITERAL 
%token NULL

/* ( ) () { } [ ] .. ... */
%token LPAR RPAR LPARRPAR LBRACE RBRACE LSQUARE RSQUARE DOTDOT DOTDOTDOT

/* ; ;; , : . ? */
%token SEMICOLON SEMISEMI COMMA COLON DOT QUESTION

/* - -- + ++ * / % */
%token MINUS MINUSMINUS PLUS PLUSPLUS STAR SLASH PERCENT
 
/* = <= >= > < == != <: :> */
%token EQ LTEQ GTEQ GT LT EQEQ BANGEQ LTCOLON COLONGT

/* += -= *= /= %= */
%token PLUSEQ MINUSEQ STAREQ SLASHEQ PERCENTEQ

/* && || => <=> ! */
%token AMPAMP BARBAR EQEQGT LTEQEQGT EXCLAM

/* if then else return while break for fo break continue case switch default goto */
%token IF THEN ELSE RETURN WHILE FOR DO BREAK CONTINUE CASE SWITCH DEFAULT GOTO LOOP

/* exception of throw try catch finally new free let in var */
%token EXCEPTION OF THROW TRY CATCH FINALLY NEW FREE LET IN VAR

/* pack unpack assert */
%token ABSTRACT PACK UNPACK ASSERT ASSUME HINT CHECK

/* type invariant logic axiomatic with variant and axiom tag */
%token TYPE INVARIANT LOGIC PREDICATE AXIOMATIC WITH VARIANT 
%token AND AXIOM LEMMA TAG

/* integer boolean real double unit void rep */
%token INTEGER BOOLEAN REAL DOUBLE FLOAT UNIT REP

/* assigns allocates assumes behavior ensures requires decreases throws reads */
%token ASSIGNS ALLOCATES ASSUMES BEHAVIOR ENSURES REQUIRES DECREASES THROWS READS

/* \forall \exists \offset_max \offset_min \address \old \result \mutable \typeof \bottom \typeeq \absolute_address */
%token BSFORALL BSEXISTS BSOFFSET_MAX BSOFFSET_MIN BSADDRESS BSOLD BSAT BSFRESH
%token BSRESULT BSMUTABLE BSTYPEOF BSBOTTOM BSTYPEEQ BSABSOLUTE_ADDRESS
%token BSBASE_BLOCK

/* \nothing */
%token BSNOTHING

/* as _ match -> end */
%token AS UNDERSCORE MATCH MINUSGT END

/* & ~ ^ | << >> >>> */
%token AMP TILDE HAT PIPE LSHIFT LRSHIFT ARSHIFT
/* | with greater priority */
%token ALT

/* |= &= ^= */
%token BAREQ AMPEQ CARETEQ

/* @ (string concat) */
%token AT

%token PRAGMA_GEN_SEP PRAGMA_GEN_FRAME PRAGMA_GEN_SUB  PRAGMA_GEN_SAME

%token EOF
%type <Jc_ast.pexpr Jc_ast.decl list> file
%start file

/* precedences on expressions (from lowest to highest) */

%nonassoc PRECLOOPANNOT
%nonassoc FOR

%nonassoc PRECIF THEN
%nonassoc ELSE

%nonassoc PRECTRY
%nonassoc FINALLY

%nonassoc PRECLOGIC
%nonassoc EQ

%nonassoc PRECTYPE
/* and */
%right AND

/* precedences on expressions  */

%nonassoc RETURN ASSERT ASSUME THROW HINT precwhile CHECK
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
%left pipe_trigger
%left ALT
%left AS
%left HAT
%left AMP
%left LT GT LTEQ GTEQ EQEQ BANGEQ LTCOLON COLONGT
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
| tag_and_type_decl file
    { let tag, ty = $1 in tag::ty::$2 }
| EOF 
    { [] }
;

decl: 
| variable_definition
    { $1 }
| function_definition
    { $1 }
| tag_definition
    { $1 }
| type_definition
    { $1 }
/*
| axiom_definition
    { $1 }
*/
| global_invariant_definition
    { $1 }
| exception_definition
    { $1 }
| logic_definition
    { $1 }
| pragma_gen_sep 
    { $1 }
/*
| error
    { Jc_options.parsing_error (pos ()) "'type' or type expression expected" }
*/
;


/*******************/
/* type definition */	      
/*******************/

type_definition:
| TYPE IDENTIFIER EQ int_constant DOTDOT int_constant
    { locate (JCDenum_type($2,$4,$6)) }
/*
| LOGIC TYPE IDENTIFIER
    { locate (JCDlogic_type($3)) }
*/
| TYPE IDENTIFIER EQ LSQUARE variant_tag_list RSQUARE
    { locate (JCDvariant_type($2, $5)) }
| TYPE IDENTIFIER EQ LSQUARE union_tag_list RSQUARE
    { locate (JCDunion_type($2,false,$5)) }
| TYPE IDENTIFIER EQ LSQUARE discr_union_tag_list RSQUARE
    { locate (JCDunion_type($2,true,$5)) }
;

int_constant:
| CONSTANT 
    { num_of_constant (pos_i 1)$1 }
| MINUS CONSTANT
    { Num.minus_num (num_of_constant (pos_i 2) $2) }
;

variant_tag_list:
| identifier PIPE variant_tag_list
    { $1::$3 }
| identifier
    { [ $1 ] }
;

union_tag_list:
| identifier AMP union_tag_list
    { $1::$3 }
| identifier AMP identifier
    { [ $1; $3 ] }
;

discr_union_tag_list:
| identifier HAT discr_union_tag_list
    { $1::$3 }
| identifier HAT identifier
    { [ $1; $3 ] }
;

/******************/
/* tag definition */
/******************/

tag_definition:
| TAG IDENTIFIER LT type_parameter_names GT EQ
    extends LBRACE field_declaration_list RBRACE
    { let (f,i) = $9 in locate (JCDtag($2,$4,$7,f,i)) }
| TAG IDENTIFIER EQ
    extends LBRACE field_declaration_list RBRACE
    { let (f,i) = $6 in locate (JCDtag($2,[],$4,f,i)) }
;

type_parameter_names:
| IDENTIFIER COMMA type_parameter_names
    { $1::$3 }
| IDENTIFIER
    { [$1] }
;

extends:
| /* epsilon */
    { None }
| IDENTIFIER WITH
    { Some($1, []) }
| IDENTIFIER LT type_parameters GT WITH
    { Some($1, $3) }
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
| field_modifier type_expr IDENTIFIER SEMICOLON
    { ($1, $2, $3, None) }
| field_modifier type_expr IDENTIFIER COLON int_constant SEMICOLON
    { ($1, $2, $3, Some (Num.int_of_num $5)) }
;

field_modifier:
| /* epsilon */
    { (false,false) }
| REP
    { (true,false) }
| ABSTRACT
    { (true,true) }
;        

invariant:
| INVARIANT identifier LPAR IDENTIFIER RPAR EQ expression SEMICOLON
    { ($2,$4,$7) }
;

/********************************/
/* tag and type syntactic suger */
/********************************/

tag_and_type_decl:
| TYPE IDENTIFIER EQ extends LBRACE field_declaration_list RBRACE
    { let (f,i) = $6 in
      let id = locate_identifier $2 in
      locate (JCDtag($2, [], $4, f, i)),
      locate (JCDvariant_type($2, [id])) }
| TYPE IDENTIFIER LT type_parameter_names GT EQ
    extends LBRACE field_declaration_list RBRACE
    { let (f,i) = $9 in
      let id = locate_identifier $2 in
      locate (JCDtag($2, $4, $7, f, i)),
      locate (JCDvariant_type($2, [id])) }
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
    { (true,$1,$2) }
| EXCLAM type_expr IDENTIFIER
    { (false,$2,$3) }
;


type_expr:
| INTEGER
    { locate (JCPTnative Tinteger) }
| BOOLEAN
    { locate (JCPTnative Tboolean) }
| REAL
    { locate (JCPTnative Treal) }
| DOUBLE
    { locate (JCPTnative (Tgenfloat `Double)) }
| FLOAT
    { locate (JCPTnative (Tgenfloat `Float)) }
| UNIT
    { locate (JCPTnative Tunit) }
| IDENTIFIER 
    { locate (JCPTidentifier ($1,[])) }
| IDENTIFIER  LT type_parameters GT
    { locate (JCPTidentifier ($1,$3)) }
| IDENTIFIER LSQUARE DOTDOT RSQUARE
    { locate (JCPTpointer($1,[],None,None)) }
| IDENTIFIER LSQUARE int_constant RSQUARE
    { let n = $3 in
      locate (JCPTpointer($1,[],Some n,Some n)) }
| IDENTIFIER LSQUARE int_constant DOTDOT RSQUARE
    { let n = $3 in
      locate (JCPTpointer($1,[],Some n,None)) }
| IDENTIFIER LSQUARE int_constant DOTDOT int_constant RSQUARE
    { let n, m = $3, $5 in
      locate (JCPTpointer($1,[],Some n,Some m)) }
| IDENTIFIER LSQUARE DOTDOT int_constant RSQUARE
    { let m = $4 in
      locate (JCPTpointer($1,[],None,Some m)) }

| IDENTIFIER LT type_parameters GT LSQUARE DOTDOT RSQUARE
    { locate (JCPTpointer($1,$3,None,None)) }
| IDENTIFIER LT type_parameters GT LSQUARE int_constant RSQUARE
    { let n = $6 in
      locate (JCPTpointer($1,$3,Some n,Some n)) }
| IDENTIFIER LT type_parameters GT LSQUARE int_constant DOTDOT RSQUARE
    { let n = $6 in
      locate (JCPTpointer($1,$3,Some n,None)) }
| IDENTIFIER LT type_parameters GT
    LSQUARE int_constant DOTDOT int_constant RSQUARE
    { let n, m = $6, $8 in
      locate (JCPTpointer($1,$3,Some n,Some m)) }
| IDENTIFIER LT type_parameters GT LSQUARE DOTDOT int_constant RSQUARE
    { let m = $7 in
      locate (JCPTpointer($1,$3,None,Some m)) }
;

type_parameters:
| type_expr COMMA type_parameters
    { $1::$3 }
| type_expr
    { [$1] }
;

function_specification:
| /* epsilon */ 
    { [] }
| spec_clause function_specification 
    { $1::$2 }
;

spec_clause:
| REQUIRES expression SEMICOLON
    { JCCrequires($2) }
| DECREASES expression SEMICOLON
    { JCCdecreases($2,None) }
| DECREASES expression FOR identifier SEMICOLON
    { JCCdecreases($2,Some $4) }
| behavior
  { JCCbehavior $1 }
;

behavior:
| BEHAVIOR ident_or_default COLON throws assumes requires assigns_opt
  allocates_opt ENSURES expression SEMICOLON
    { (pos_i 2,$2,$4,$5,$6,$7,$8,$10) }
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

assigns_opt:
| /* epsilon */
    { None }
| assigns
    { $1 }
;

assigns:
| ASSIGNS argument_expression_list SEMICOLON
    { Some(pos_i 2,$2) }
| ASSIGNS BSNOTHING SEMICOLON
    { Some (pos_i 2,[]) }
;

allocates_opt:
| /* epsilon */
    { None }
| allocates
    { $1 }
;

allocates:
| ALLOCATES argument_expression_list SEMICOLON
    { Some(pos_i 2,$2) }
| ALLOCATES BSNOTHING SEMICOLON
    { Some (pos_i 2,[]) }
;

reads:
| 
    { JCnone }
| READS argument_expression_list SEMICOLON
    { JCreads $2 }
| READS BSNOTHING SEMICOLON
    { JCreads [] }
;

function_definition: 
| type_expr identifier parameters function_specification compound_expr
    { locate (JCDfun($1, $2, $3, $4, Some $5)) }
| type_expr identifier parameters function_specification SEMICOLON
    { locate (JCDfun($1, $2, $3, $4, None)) }
;


/******************************/
/* Global variable definition */
/******************************/

variable_definition:
| type_expr IDENTIFIER EQ expression SEMICOLON
    { locate (JCDvar($1,$2,Some $4)) }
| type_expr IDENTIFIER SEMICOLON
    { locate (JCDvar($1,$2,None)) }
;

/********************/
/* global invariant */
/********************/

global_invariant_definition:
| INVARIANT IDENTIFIER COLON expression
    { locate( JCDglobal_inv($2,$4)) }
;


/*************************/
/* exception definitions */
/*************************/

exception_definition:
| EXCEPTION IDENTIFIER OF type_expr
    { locate (JCDexception($2,Some $4)) }
;


/***************/
/* expressions */
/***************/

primary_expression: 
| IDENTIFIER 
    { locate (JCPEvar $1) }
| BSRESULT
    { locate (JCPEvar "\\result") }
| CONSTANT 
    { locate (JCPEconst $1) }
| LPARRPAR 
    { locate (JCPEconst JCCvoid) }
| NULL 
    { locate (JCPEconst JCCnull) }
| STRING_LITERAL 
    { locate (JCPEconst (JCCstring $1)) }
| LPAR expression COLONGT type_expr RPAR
    { locate (JCPEcast($2, $4)) }
| LPAR expression RPAR 
    { $2 }
| LPAR IDENTIFIER COLON expression RPAR
    { locate (JCPElabel($2,$4)) }
;

postfix_expression: 
| primary_expression 
    { $1 }
| IDENTIFIER label_binders LPAR argument_expression_list_opt RPAR 
    { locate (JCPEapp($1, $2, $4)) }
| IDENTIFIER label_binders LPARRPAR 
    { locate (JCPEapp($1, $2, [])) }
| BSFRESH LPAR expression RPAR 
    { locate (JCPEfresh($3)) }
| BSOLD LPAR expression RPAR 
    { locate (JCPEold($3)) }
| BSAT LPAR expression COMMA IDENTIFIER RPAR 
    { locate (JCPEat($3,label $5)) }
| BSOFFSET_MAX LPAR expression RPAR 
    { locate (JCPEoffset(Offset_max,$3)) }
| BSOFFSET_MIN LPAR expression RPAR 
    { locate (JCPEoffset(Offset_min,$3)) }
| BSADDRESS LPAR expression RPAR 
    { locate (JCPEaddress(Addr_pointer,$3)) }
| BSABSOLUTE_ADDRESS LPAR expression RPAR 
    { locate (JCPEaddress(Addr_absolute,$3)) }
| BSBASE_BLOCK LPAR expression RPAR 
    { locate (JCPEbase_block($3)) }
| postfix_expression DOT IDENTIFIER
    { locate (JCPEderef ($1, $3)) }
| postfix_expression PLUSPLUS 
    { locate (JCPEunary (`Upostfix_inc, $1)) }
| postfix_expression MINUSMINUS
    { locate (JCPEunary (`Upostfix_dec, $1)) }
| PLUSPLUS postfix_expression 
    { locate (JCPEunary (`Uprefix_inc, $2)) }
| MINUSMINUS postfix_expression 
    { locate (JCPEunary (`Uprefix_dec, $2)) }
| PLUS postfix_expression %prec UPLUS
    { locate (JCPEunary (`Uplus, $2)) }
| MINUS postfix_expression %prec UMINUS
    { locate (JCPEunary (`Uminus, $2)) }
| TILDE postfix_expression 
    { locate (JCPEunary (`Ubw_not, $2)) }
| EXCLAM postfix_expression 
    { locate (JCPEunary (`Unot, $2)) }
| LSQUARE expression DOTDOT expression RSQUARE
    { locate (JCPErange(Some $2,Some $4)) }
| LSQUARE DOTDOT expression RSQUARE 
    { locate (JCPErange(None,Some $3)) }
| LSQUARE expression DOTDOT RSQUARE 
    { locate (JCPErange(Some $2,None)) }
| LSQUARE DOTDOT RSQUARE 
    { locate (JCPErange(None,None)) }
;

label_binders:
| /* epsilon */ { [] }
| LBRACE IDENTIFIER label_list_end RBRACE { (label $2)::$3 }
;

label_list_end:
| /* epsilon */ { [] }
| COMMA IDENTIFIER label_list_end { (label $2)::$3 }
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
    { locate (JCPEbinary ($1, `Bmul, $3)) }
| multiplicative_expression SLASH postfix_expression 
    { locate (JCPEbinary ($1, `Bdiv, $3)) }
| multiplicative_expression PERCENT postfix_expression 
    { locate (JCPEbinary ($1, `Bmod, $3)) }
;

additive_expression: 
| multiplicative_expression 
    { $1 }
| additive_expression PLUS multiplicative_expression 
    { locate (JCPEbinary ($1, `Badd, $3)) }
| additive_expression MINUS multiplicative_expression 
    { locate (JCPEbinary ($1, `Bsub, $3)) }
| additive_expression AT multiplicative_expression 
    { locate (JCPEbinary ($1, `Bconcat, $3)) }
;

shift_expression: 
| additive_expression 
    { $1 }
| shift_expression LSHIFT additive_expression 
    { locate (JCPEbinary ($1, `Bshift_left, $3)) }
| shift_expression LRSHIFT additive_expression 
    { locate (JCPEbinary ($1, `Blogical_shift_right, $3)) }
| shift_expression ARSHIFT additive_expression 
    { locate (JCPEbinary ($1, `Barith_shift_right, $3)) }
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
| compound_expr
    { $1 }
| ASSERT FOR identifier_list COLON expression %prec FOR
    { locate (JCPEassert($3,Aassert,$5)) }
| ASSERT expression 
    { locate (JCPEassert([],Aassert,$2)) }
| HINT FOR identifier_list COLON expression %prec FOR
    { locate (JCPEassert($3,Ahint,$5)) }
| HINT expression 
    { locate (JCPEassert([],Ahint,$2)) }
| ASSUME FOR identifier_list COLON expression %prec FOR
    { locate (JCPEassert($3,Aassume,$5)) }
| ASSUME expression 
    { locate (JCPEassert([],Aassume,$2)) }
| CHECK FOR identifier_list COLON expression %prec FOR
    { locate (JCPEassert($3,Acheck,$5)) }
| CHECK expression 
    { locate (JCPEassert([],Acheck,$2)) }
| requires behavior compound_expr
    { locate (JCPEcontract($1,None,[$2],$3)) } 
| iteration_expression 
    { $1 }
| jump_expression 
    { $1 }
| declaration
    { $1 }
/*
| SPEC expression { locate (CSspec ($1,$2)) }
*/
| pack_expression { $1 }
| exception_expression { $1 }
| shift_expression 
    { $1 }
| SWITCH LPAR expression RPAR LBRACE switch_block RBRACE
    { locate (JCPEswitch ($3, $6)) }

| NEW IDENTIFIER LSQUARE expression RSQUARE
    { locate (JCPEalloc ($4, $2)) }
| FREE LPAR expression RPAR
    { locate (JCPEfree $3) }
| expression LT expression 
    { locate (JCPEbinary ($1, `Blt, $3)) }
| expression GT expression
    { locate (JCPEbinary ($1, `Bgt, $3)) }
| expression LTEQ expression
    { locate (JCPEbinary ($1, `Ble, $3)) }
| expression GTEQ expression
    { locate (JCPEbinary ($1, `Bge, $3)) }
| expression LTCOLON IDENTIFIER
    { locate (JCPEinstanceof($1, $3)) }
| expression EQEQ expression 
    { locate (JCPEbinary ($1, `Beq, $3)) }
| expression BANGEQ expression 
    { locate (JCPEbinary ($1, `Bneq, $3)) }
| expression AMP expression 
    { locate (JCPEbinary ($1, `Bbw_and, $3)) }
| expression HAT expression 
    { locate (JCPEbinary ($1, `Bbw_xor, $3)) }
| expression PIPE expression
    { locate (JCPEbinary ($1, `Bbw_or, $3)) }
| expression AMPAMP expression 
    { locate (JCPEbinary($1, `Bland, $3)) }
| expression BARBAR expression 
    { locate (JCPEbinary($1, `Blor, $3)) }
| IF expression THEN expression ELSE expression
    { locate (JCPEif ($2, $4, $6)) }
| IF expression THEN expression
    { locate (JCPEif ($2, $4, skip)) }
| LET IDENTIFIER EQ expression IN expression %prec PRECFORALL
    { locate (JCPElet (None, $2, Some $4, $6)) }
| LET type_expr IDENTIFIER EQ expression IN expression %prec PRECFORALL
    { locate (JCPElet (Some $2, $3, Some $5, $7)) }
| postfix_expression assignment_operator expression %prec ASSIGNOP
    { let a  =
	match $2 with
		| `Aeq -> JCPEassign ($1, $3)
		| `Aadd -> JCPEassign_op ($1, `Badd, $3)
		| `Asub -> JCPEassign_op ($1, `Bsub, $3)
		| `Amul -> JCPEassign_op ($1, `Bmul, $3)
		| `Adiv -> JCPEassign_op ($1, `Bdiv, $3)
		| `Amod -> JCPEassign_op ($1, `Bmod, $3)
		| `Aand -> JCPEassign_op ($1, `Bbw_and, $3)
		| `Axor -> JCPEassign_op ($1, `Bbw_xor, $3)
		| `Aor -> JCPEassign_op ($1, `Bbw_or, $3)
(*
		| Aleft -> CEassign_op ($1, `Bshift_left, $3)
		| Aright -> CEassign_op ($1, `Bshift_right, $3)
*)
      in locate a }

| BSFORALL type_expr identifier_list triggers SEMICOLON expression 
    %prec PRECFORALL
    { locate (JCPEquantifier(Forall,$2,$3,$4,$6)) }
| BSEXISTS type_expr identifier_list triggers SEMICOLON expression 
    %prec PRECFORALL
    { locate (JCPEquantifier(Exists,$2,$3,$4,$6)) }
| expression EQEQGT expression
    { locate (JCPEbinary($1,`Bimplies,$3)) }
| expression LTEQEQGT expression
    { locate (JCPEbinary($1,`Biff,$3)) }
/*
| expression COMMA assignment_expression { locate (CEseq ($1, $3)) }
*/
| BSMUTABLE LPAR expression COMMA tag RPAR
    { locate (JCPEmutable($3, $5)) }
| BSMUTABLE LPAR expression RPAR
    { locate (JCPEmutable($3, locate JCPTbottom)) }
| BSTYPEEQ LPAR tag COMMA tag RPAR
    { locate (JCPEeqtype($3, $5)) }
| MATCH expression WITH pattern_expression_list END
    { locate (JCPEmatch($2, $4)) }
;

tag:
| identifier
    { locate (JCPTtag $1) }
| BSBOTTOM
    { locate JCPTbottom }
| BSTYPEOF LPAR expression RPAR
    { locate (JCPTtypeof $3) }
;

identifier_list: 
| identifier 
    { [$1] }
| identifier COMMA identifier_list 
    { $1 :: $3 }
;

identifier:
| DEFAULT
    { locate_identifier "default" }
| IDENTIFIER
    { locate_identifier $1 }
;

triggers:
| /* epsilon */ { [] }
| LSQUARE list1_trigger_sep_bar RSQUARE { $2 }
;

list1_trigger_sep_bar:
| trigger { [$1] }
| trigger PIPE list1_trigger_sep_bar  %prec pipe_trigger { $1 :: $3 }
;

trigger:
  argument_expression_list { $1 }
;

/****************/
/* declarations */
/****************/


declaration: 
| VAR type_expr IDENTIFIER
    { locate (JCPEdecl($2, $3, None)) }
| VAR type_expr IDENTIFIER EQ expression
    { locate (JCPEdecl($2, $3, Some $5)) }
;


/**************/
/* expressions */
/**************/

compound_expr:
| LBRACE expression_list RBRACE
    { locate (JCPEblock $2) }
;

expression_list: 
| expression SEMICOLON
    { [$1] }
| expression
    { [$1] }
| expression SEMICOLON expression_list 
    { $1 :: $3 }
;

switch_block: 
| /* $\varepsilon$ */
    { [] }
| switch_labels 
    { [($1, locate (JCPEblock []))] }
| switch_labels expression_list switch_block
    { ($1, locate (JCPEblock $2))::$3 }
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

iteration_expression: 
| loop_annot WHILE LPAR expression RPAR expression %prec precwhile
    { let (i,v) = $1 in 
      locate (JCPEwhile ($4, i, v, $6)) }
| loop_annot DO expression WHILE LPAR expression RPAR
    { assert false (* TODO locate (JCPEdowhile ($1, $3, $6)) *) }
| loop_annot FOR LPAR argument_expression_list_opt SEMICOLON expression SEMICOLON 
    argument_expression_list_opt RPAR expression %prec precwhile
    { let (i,v) = $1 in 
      (*
	let i = match i with 
	| [] -> locate (JCPEconst(JCCboolean true))
	| [_,p] -> p
	|  _ -> assert false
      in
      *)
      locate (JCPEfor($4, $6, $8, i, v, $10)) }
;


loop_behavior:
| INVARIANT expression SEMICOLON assigns_opt
    { (Some $2,$4) }
| assigns
    { (None,$1) }
;

loop_for_behavior_list:
| BEHAVIOR identifier_list COLON loop_behavior loop_for_behavior_list
    { let (i,a) = $4 in ($2,i,a) :: $5 }
| /* epsilon */
    { [] }
;

loop_behaviors:
| loop_behavior loop_for_behavior_list
    { let (i,a) = $1 in ([],i,a)::$2 }
| loop_for_behavior_list
    { $1 }
;

loop_annot:
| LOOP loop_behaviors VARIANT expression SEMICOLON
    { ($2, Some ($4,None)) }
| LOOP loop_behaviors VARIANT expression FOR identifier SEMICOLON
    { ($2, Some ($4, Some $6)) }
| LOOP loop_behaviors
    { ($2, None) }
;

jump_expression: 
| GOTO identifier
    { locate (JCPEgoto $2#name) }
/*
| CONTINUE SEMICOLON { locate CScontinue }
*/
| BREAK
    { locate (JCPEbreak "") }
| RETURN expression
    { locate (JCPEreturn $2) }
;

pack_expression:
| PACK LPAR expression COMMA identifier RPAR
    { locate (JCPEpack ($3, Some $5)) }
| PACK LPAR expression RPAR
    { locate (JCPEpack ($3, None)) }
| UNPACK LPAR expression COMMA identifier RPAR
    { locate (JCPEunpack ($3, Some $5)) }
| UNPACK LPAR expression RPAR
    { locate (JCPEunpack ($3, None)) }
;

catch_expression: 
| CATCH identifier IDENTIFIER expression
    { ($2, $3, $4) }
;

catch_expression_list:
| catch_expression
    { [$1] }
| catch_expression catch_expression_list 
    { $1 :: $2 }
;

exception_expression:
| THROW identifier expression
   { locate (JCPEthrow($2,$3)) }
| TRY expression catch_expression_list END
   { locate (JCPEtry($2, $3, skip)) }
| TRY expression catch_expression_list FINALLY expression END
   { locate (JCPEtry($2, $3, $5)) }
;

/**********************************/
/* Logic functions and predicates */
/**********************************/

logic_definition:
/* constants def */
| LOGIC type_expr IDENTIFIER logic_type_arg EQ expression
    { locate (JCDlogic(Some $2, $3, $4, [], [], JCexpr $6)) }
/* constants no def */
| LOGIC type_expr IDENTIFIER logic_type_arg
    { locate (JCDlogic(Some $2, $3, $4 , [], [], JCreads [])) }
/* logic fun def */
| LOGIC type_expr IDENTIFIER logic_type_arg label_binders parameters EQ expression
    { let p = lparams $6 in
      locate (JCDlogic(Some $2, $3, $4 , $5, p, JCexpr $8)) }
/* logic pred def */
| PREDICATE IDENTIFIER logic_type_arg label_binders parameters EQ expression
    { let p = lparams $5 in
      locate (JCDlogic(None, $2, $3  ,$4, p, JCexpr $7)) }
/* logic fun reads */
/*
| LOGIC type_expr IDENTIFIER logic_type_arg label_binders parameters reads %prec PRECLOGIC
    { locate (JCDlogic(Some $2, $3, $4 ,$5, $6, JCreads $7)) }
*/
/* logic pred reads */
/*
| PREDICATE IDENTIFIER logic_type_arg label_binders parameters reads %prec PRECLOGIC
    { locate (JCDlogic(None, $2, $3 ,$4, $5, JCreads $6)) }
*/
/* logic fun axiomatic def */
/*
| LOGIC type_expr IDENTIFIER logic_type_arg label_binders parameters LBRACE axioms RBRACE
    { locate (JCDlogic(Some $2, $3, $4 ,$5, $6, JCaxiomatic $8)) }
*/
/* logic pred axiomatic def */
/*
| PREDICATE IDENTIFIER logic_type_arg label_binders parameters LBRACE axioms RBRACE
    { locate (JCDlogic(None, $2, $3, $4, $5, JCaxiomatic $7)) }
*/
/* logic pred inductive def */
| PREDICATE IDENTIFIER logic_type_arg label_binders parameters LBRACE indcases RBRACE
    { let p = lparams $5 in
      locate (JCDlogic(None, $2, $3 ,$4 , p, JCinductive $7)) }
| AXIOMATIC IDENTIFIER LBRACE logic_declarations RBRACE
    { locate (JCDaxiomatic($2,$4)) } 
| LEMMA IDENTIFIER logic_type_arg label_binders COLON expression
    { locate( JCDlemma($2,false,$3,$4,$6)) }
;




logic_declarations:
| logic_declaration
    { [$1] }
| logic_declaration logic_declarations
    { $1::$2 }
;

string_list:
| IDENTIFIER {[$1]}
| IDENTIFIER COMMA string_list {$1::$3}

logic_type_arg:
| {[]}
| LT string_list GT {$2}

logic_declaration:
| logic_definition
    { $1 }
| LOGIC TYPE IDENTIFIER logic_type_arg
    { locate (JCDlogic_type($3,$4)) }
/* remove this comment if removed from logic_definition
| LOGIC type_expr IDENTIFIER 
    { locate (JCDlogic(Some $2, $3, [], [], JCnone)) }
*/
| PREDICATE IDENTIFIER logic_type_arg label_binders parameters reads
    { let p = lparams $5 in
      locate (JCDlogic(None, $2, $3, $4, p, $6)) }
| LOGIC type_expr IDENTIFIER logic_type_arg label_binders parameters reads
	{ let p = lparams $6 in
	  locate (JCDlogic(Some $2, $3, $4, $5, p, $7)) }
| AXIOM identifier logic_type_arg label_binders COLON expression
    { locate( JCDlemma($2#name,true,$3,$4,$6)) }
;

indcases:
| /* epsilon */
    { [] }
| CASE identifier label_binders COLON expression SEMICOLON indcases
    { ($2,$3,$5)::$7 }
;

/************/
/* patterns */
/************/

pattern:
| identifier LBRACE field_patterns RBRACE
    { locate (JCPPstruct($1, $3)) }
| identifier
    { locate (JCPPvar $1) }
| LPAR pattern RPAR
    { $2 }
| pattern PIPE pattern
    { locate (JCPPor($1, $3)) }
| pattern AS identifier
    { locate (JCPPas($1, $3)) }
| UNDERSCORE
    { locate JCPPany }
| CONSTANT 
    { locate (JCPPconst $1) }
| LPARRPAR 
    { locate (JCPPconst JCCvoid) }
| NULL 
    { locate (JCPPconst JCCnull) }
;

field_patterns:
| identifier EQ pattern SEMICOLON field_patterns
    { ($1, $3)::$5 }
|
    { [] }
;

/*Multiply defined : Does ocamlyacc take the last. In fact it seems to take the first (cf. variant.jc)*/
pattern_expression_list:
| pattern MINUSGT expression SEMICOLON pattern_expression_list
    { ($1, $3)::$5 }
| pattern MINUSGT expression SEMICOLON
    { [$1, $3] }
;


/*pattern_expression_list:
| pattern MINUSGT compound_expr pattern_expression_list
    { ($1, $3)::$4 }
| pattern MINUSGT compound_expr
    { [$1, $3] }
;*/

/**************/
/* pragma_gen_sep */
/**************/
pragma_gen_sep:
| PRAGMA_GEN_SEP IDENTIFIER type_expr_parameters
    { locate (JCDpragma_gen_sep("",$2, $3)) }
| PRAGMA_GEN_SEP IDENTIFIER IDENTIFIER type_expr_parameters
    { locate (JCDpragma_gen_sep($2,$3, $4)) }
| PRAGMA_GEN_FRAME IDENTIFIER IDENTIFIER
    { locate (JCDpragma_gen_frame($2,$3)) }
| PRAGMA_GEN_SUB IDENTIFIER IDENTIFIER
    { locate (JCDpragma_gen_sub($2,$3)) }
| PRAGMA_GEN_SAME IDENTIFIER IDENTIFIER
    { locate (JCDpragma_gen_same($2,$3)) }
;

type_expr_parameters:
| LPARRPAR
    { [] }
| LPAR RPAR
    { [] }
| LPAR type_expr_comma_list RPAR
    { $2 } 
;

type_expr_restreint:
|type_expr {$1,[]}
|type_expr PIPE LPAR type_parameter_names RPAR {$1,$4}

type_expr_comma_list: 
| type_expr_restreint
    { [$1] }
| type_expr_restreint COMMA type_expr_comma_list
    { $1 :: $3 }
;

/*
Local Variables: 
compile-command: "LC_ALL=C make -C .. byte"
End: 
*/
