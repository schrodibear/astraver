/*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

/* from http://www.lysator.liu.se/c/ANSI-C-grammar-y.html */

%{

  open Logic
  open Ptree
  open Cast
  open Parsing

  let loc () = (symbol_start (), symbol_end ())
  let loc_i i = (rhs_start i, rhs_end i)

  let uns () =
    raise (Stdpp.Exc_located (loc (), Stream.Error "Unsupported C syntax"))

%}

%token <int * string> ANNOT

%token <string> IDENTIFIER CONSTANT STRING_LITERAL TYPE_NAME
%token SIZEOF
%token PTR_OP INC_OP DEC_OP LEFT_OP RIGHT_OP LE_OP GE_OP EQ_OP NE_OP
%token AND_OP OR_OP MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN
%token SUB_ASSIGN LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN
%token XOR_ASSIGN OR_ASSIGN

%token TYPEDEF EXTERN STATIC AUTO REGISTER
%token CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE CONST VOLATILE VOID
%token STRUCT UNION ENUM ELLIPSIS

%token CASE DEFAULT IF ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN

%token SEMICOLON LBRACE RBRACE COMMA COLON EQUAL LPAR RPAR LSQUARE RSQUARE
%token DOT AMP EXL TILDE MINUS PLUS STAR SLASH PERCENT LT GT HAT PIPE
%token QUESTION EOF

%type <Cast.file> file
%start file
%%

file
        : translation_unit EOF { $1 }
        | EOF { [] }
        ;

primary_expression
        : IDENTIFIER { CEvar (loc (), Ident.create $1) }
        | CONSTANT { CEconst (loc (), $1) }
        | STRING_LITERAL { uns() }
        | LPAR expression RPAR { $2 }
        ;

postfix_expression
        : primary_expression 
            { $1 }
        | postfix_expression LSQUARE expression RSQUARE 
	    { CEarrget (loc (), $1, $3) }
        | postfix_expression LPAR RPAR 
	    { CEcall (loc (), $1, []) }
        | postfix_expression LPAR argument_expression_list RPAR 
	    { CEcall (loc (), $1, $3) }
        | postfix_expression DOT IDENTIFIER 
	    { uns () }
        | postfix_expression PTR_OP IDENTIFIER 
	    { uns() }
        | postfix_expression INC_OP 
	    { CEunary (loc (), Postfix_inc, $1) }
        | postfix_expression DEC_OP
	    { CEunary (loc (), Postfix_dec, $1)}
        ;

argument_expression_list
        : assignment_expression { [$1] }
        | argument_expression_list COMMA assignment_expression { $1 @ [$3] }
        ;

unary_expression
        : postfix_expression { $1 }
        | INC_OP unary_expression { CEunary (loc (), Prefix_inc, $2) }
        | DEC_OP unary_expression { CEunary (loc (), Prefix_dec, $2) }
        | unary_operator cast_expression { uns () }
        | SIZEOF unary_expression { uns () }
        | SIZEOF LPAR type_name RPAR { uns () }
        ;

unary_operator
        : AMP { uns () }
        | STAR { uns () }
        | PLUS { Uplus }
        | MINUS { Uminus }
        | TILDE { uns () }
        | EXL { Not }
        ;

cast_expression
        : unary_expression { $1 }
        | LPAR type_name RPAR cast_expression { uns () }
        ;

multiplicative_expression
        : cast_expression 
            { $1 }
        | multiplicative_expression STAR cast_expression 
	    { CEbinary (loc (), $1, Mult, $3) }
        | multiplicative_expression SLASH cast_expression 
	    { CEbinary (loc (), $1, Div, $3) }
        | multiplicative_expression PERCENT cast_expression 
	    { CEbinary (loc (), $1, Mod, $3) }
        ;

additive_expression
        : multiplicative_expression 
           { $1 }
        | additive_expression PLUS multiplicative_expression 
	    { CEbinary (loc (), $1, Plus, $3) }
        | additive_expression MINUS multiplicative_expression 
	    { CEbinary (loc (), $1, Minus, $3) }
        ;

shift_expression
        : additive_expression { $1 }
        | shift_expression LEFT_OP additive_expression { uns () }
        | shift_expression RIGHT_OP additive_expression { uns () }
        ;

relational_expression
        : shift_expression 
            { $1 }
        | relational_expression LT shift_expression 
	    { CEbinary (loc (), $1, Lt, $3) }
        | relational_expression GT shift_expression
	    { CEbinary (loc (), $1, Gt, $3) }
        | relational_expression LE_OP shift_expression
	    { CEbinary (loc (), $1, Le, $3) }
        | relational_expression GE_OP shift_expression
	    { CEbinary (loc (), $1, Ge, $3) }
        ;

equality_expression
        : relational_expression 
            { $1 }
        | equality_expression EQ_OP relational_expression 
	    { CEbinary (loc (), $1, Eq, $3) }
        | equality_expression NE_OP relational_expression 
	    { CEbinary (loc (), $1, Neq, $3) }
        ;

and_expression
        : equality_expression 
            { $1 }
        | and_expression AMP equality_expression 
	    { CEbinary (loc (), $1, Bw_and, $3) }
        ;

exclusive_or_expression
        : and_expression 
            { $1 }
        | exclusive_or_expression HAT and_expression 
	    { CEbinary (loc (), $1, Bw_xor, $3) }
        ;

inclusive_or_expression
        : exclusive_or_expression 
            { $1 }
        | inclusive_or_expression PIPE exclusive_or_expression 
	    { CEbinary (loc (), $1, Bw_or, $3) }
        ;

logical_and_expression
        : inclusive_or_expression 
            { $1 }
        | logical_and_expression AND_OP inclusive_or_expression 
	    { CEbinary (loc (), $1, And, $3) }
        ;

logical_or_expression
        : logical_and_expression 
            { $1 }
        | logical_or_expression OR_OP logical_and_expression 
	    { CEbinary (loc (), $1, Or, $3) }
        ;

conditional_expression
        : logical_or_expression 
            { $1 }
        | logical_or_expression QUESTION expression COLON conditional_expression 
	    { CEcond (loc (), $1, $3, $5) }
        ;

assignment_expression
        : conditional_expression 
            { $1 }
        | unary_expression assignment_operator assignment_expression 
	    { CEassign (loc (), $1, $2, $3) }
        ;

assignment_operator
        : EQUAL { Aequal }
        | MUL_ASSIGN { Amul }
        | DIV_ASSIGN { Adiv }
        | MOD_ASSIGN { Amod }
        | ADD_ASSIGN { Aadd }
        | SUB_ASSIGN { Asub }
        | LEFT_ASSIGN { Aleft }
        | RIGHT_ASSIGN { Aright }
        | AND_ASSIGN { Aand }
        | XOR_ASSIGN { Axor }
        | OR_ASSIGN { Aor }
        ;

expression
        : assignment_expression { $1 }
        | expression COMMA assignment_expression { CEseq (loc(), $1, $3) }
        ;

constant_expression
        : conditional_expression { $1 }
        ;

declaration
        : declaration_specifiers SEMICOLON { uns() }
        | declaration_specifiers init_declarator_list SEMICOLON 
	    { List.map (fun d -> Ctypedecl (loc(), d, $1)) $2 }
        ;

declaration_specifiers
        : storage_class_specifier { uns() }
        | storage_class_specifier declaration_specifiers { uns() }
        | type_specifier { $1 }
        | type_specifier declaration_specifiers { uns() }
        | type_qualifier { uns() }
        | type_qualifier declaration_specifiers { uns() }
        ;

init_declarator_list
        : init_declarator { [$1] }
        | init_declarator_list COMMA init_declarator { $1 @ [$3] }
        ;

init_declarator
        : declarator { $1 }
        | declarator EQUAL c_initializer { uns() }
        ;

storage_class_specifier
        : TYPEDEF { }
        | EXTERN { }
        | STATIC { }
        | AUTO { }
        | REGISTER { }
        ;

type_specifier
        : VOID { PTunit }
        | CHAR { PTint }
        | SHORT { PTint }
        | INT { PTint }
        | LONG { PTint }
        | FLOAT { PTfloat }
        | DOUBLE { PTfloat }
        | SIGNED { uns() }
        | UNSIGNED { uns() }
        | struct_or_union_specifier { uns() }
        | enum_specifier { uns() }
        | TYPE_NAME { PTexternal (Ident.create $1) }
        ;

struct_or_union_specifier
        : struct_or_union IDENTIFIER LBRACE struct_declaration_list RBRACE { }
        | struct_or_union LBRACE struct_declaration_list RBRACE { }
        | struct_or_union IDENTIFIER { }
        ;

struct_or_union
        : STRUCT { }
        | UNION { }
        ;

struct_declaration_list
        : struct_declaration { }
        | struct_declaration_list struct_declaration { }
        ;

struct_declaration
        : specifier_qualifier_list struct_declarator_list SEMICOLON { }
        ;

specifier_qualifier_list
        : type_specifier specifier_qualifier_list { }
        | type_specifier { }
        | type_qualifier specifier_qualifier_list { }
        | type_qualifier { }
        ;

struct_declarator_list
        : struct_declarator { }
        | struct_declarator_list COMMA struct_declarator { }
        ;

struct_declarator
        : declarator { }
        | COLON constant_expression { }
        | declarator COLON constant_expression { }
        ;

enum_specifier
        : ENUM LBRACE enumerator_list RBRACE { }
        | ENUM IDENTIFIER LBRACE enumerator_list RBRACE { }
        | ENUM IDENTIFIER { }
        ;

enumerator_list
        : enumerator { }
        | enumerator_list COMMA enumerator { }
        ;

enumerator
        : IDENTIFIER { }
        | IDENTIFIER EQUAL constant_expression { }
        ;

type_qualifier
        : CONST { }
        | VOLATILE { }
        ;

declarator
        : pointer direct_declarator { uns() }
        | direct_declarator { $1 }
        ;

direct_declarator
        : IDENTIFIER 
            { CDvar (Ident.create $1) }
        | LPAR declarator RPAR 
	    { uns() }
        | direct_declarator LSQUARE constant_expression RSQUARE 
	    { uns() }
        | direct_declarator LSQUARE RSQUARE 
	    { uns() }
        | direct_declarator LPAR parameter_type_list RPAR annot 
	    { match $1 with CDvar id -> CDfun (id, $3, $5) | _ -> uns () }
        | direct_declarator LPAR identifier_list RPAR 
	    { uns() }
        | direct_declarator LPAR RPAR annot 
            { match $1 with CDvar id -> CDfun (id, [], $4) | _ -> uns () }
        ;

/* ADDED FOR WHY */
annot
        : ANNOT         { Some $1 }
        | /* epsilon */ { None }
        ;

pointer
        : STAR { }
        | STAR type_qualifier_list { }
        | STAR pointer { }
        | STAR type_qualifier_list pointer { }
        ;

type_qualifier_list
        : type_qualifier { }
        | type_qualifier_list type_qualifier { }
        ;


parameter_type_list
        : parameter_list { $1 }
        | parameter_list COMMA ELLIPSIS { uns() }
        ;

parameter_list
        : parameter_declaration { [$1] }
        | parameter_list COMMA parameter_declaration { $1 @ [$3] }
        ;

parameter_declaration
        : declaration_specifiers declarator 
            { ($1, match $2 with CDvar id -> id | _ -> uns()) }
        | declaration_specifiers abstract_declarator { uns() }
        | declaration_specifiers { ($1, Ident.anonymous) }
        ;

identifier_list
        : IDENTIFIER { }
        | identifier_list COMMA IDENTIFIER { }
        ;

type_name
        : specifier_qualifier_list { }
        | specifier_qualifier_list abstract_declarator { }
        ;

abstract_declarator
        : pointer { }
        | direct_abstract_declarator { }
        | pointer direct_abstract_declarator { }
        ;

direct_abstract_declarator
        : LPAR abstract_declarator RPAR { }
        | LSQUARE RSQUARE { }
        | LSQUARE constant_expression RSQUARE { }
        | direct_abstract_declarator LSQUARE RSQUARE { }
        | direct_abstract_declarator LSQUARE constant_expression RSQUARE { }
        | LPAR RPAR { }
        | LPAR parameter_type_list RPAR { }
        | direct_abstract_declarator LPAR RPAR { }
        | direct_abstract_declarator LPAR parameter_type_list RPAR { }
        ;

c_initializer
        : assignment_expression { }
        | LBRACE c_initializer_list RBRACE { }
        | LBRACE c_initializer_list COMMA RBRACE { }
        ;

c_initializer_list
        : c_initializer { }
        | c_initializer_list COMMA c_initializer { }
        ;

statement
        : labeled_statement { $1 }
        | compound_statement { CSblock (loc (), $1) }
        | expression_statement { $1 }
        | selection_statement { $1 }
        | iteration_statement { $1 }
        | jump_statement { $1 }
        ;

labeled_statement
        : IDENTIFIER COLON statement { uns () }
        | CASE constant_expression COLON statement { uns () }
        | DEFAULT COLON statement { uns () }
        ;

compound_statement
        : LBRACE RBRACE { [], [] }
        | LBRACE statement_list RBRACE { [], $2 }
        | LBRACE declaration_list RBRACE { $2, [] }
        | LBRACE declaration_list statement_list RBRACE { $2, $3 }
        ;

/* ADDED FOR WHY */
annot_compound_statement
        : annot compound_statement annot { (loc (), $1, $2, $3) }
        ;

declaration_list
        : declaration { $1 }
        | declaration_list declaration { $1 @ $2 }
        ;

statement_list
        : statement { [$1] }
        | statement_list statement { $1 @ [$2] }
        ;

expression_statement
        : SEMICOLON { CSnop (loc ()) }
        | expression SEMICOLON { CSexpr (loc (), $1) }
        ;

selection_statement
        : IF LPAR expression RPAR statement 
            { CScond (loc (), $3, $5, CSnop (loc ())) }
        | IF LPAR expression RPAR statement ELSE statement 
	    { CScond (loc (), $3, $5, $7) }
        | SWITCH LPAR expression RPAR statement 
	    { uns () }
        ;

iteration_statement
        : WHILE LPAR expression RPAR ANNOT statement 
            { CSwhile (loc (), $3, $5, $6) }
        | DO ANNOT statement WHILE LPAR expression RPAR SEMICOLON 
	    { CSdowhile (loc (), $2, $3, $6) }
        | FOR LPAR expression_statement expression_statement RPAR ANNOT statement 
	    { CSfor (loc (), $3, $4, None, $6, $7) }
        | FOR LPAR expression_statement expression_statement expression RPAR ANNOT statement 
	    { CSfor (loc (), $3, $4, Some $5, $7, $8) }
        ;

jump_statement
        : GOTO IDENTIFIER SEMICOLON { uns () }
        | CONTINUE SEMICOLON { uns () }
        | BREAK SEMICOLON { uns () }
        | RETURN SEMICOLON { uns () }
        | RETURN expression SEMICOLON { uns () }
        ;

translation_unit
        : external_declaration { $1 }
        | translation_unit external_declaration { $1 @ $2 }
        ;

external_declaration
        : function_definition { [$1] }
        | declaration { $1 }
        ;

function_definition
        : declaration_specifiers declarator declaration_list compound_statement
            { uns () }
        | declaration_specifiers declarator annot_compound_statement 
	    { match $2 with
		| CDfun (id, pl, None) -> Cfundef (loc (), id, pl, $1, $3)
		| _ -> uns () }
        | declarator declaration_list compound_statement 
	    { uns () }
        | declarator compound_statement 
	    { uns () }
        ;

%%
