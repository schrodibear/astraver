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

  let error s = raise (Stdpp.Exc_located (loc (), Stream.Error s))

  let uns () =
    raise (Stdpp.Exc_located (loc (), Stream.Error "Unsupported C syntax"))
  let unss s =
    raise (Stdpp.Exc_located (loc (), 
			      Stream.Error ("Unsupported C syntax: " ^ s)))
  let warning s =
    Format.eprintf "%a warning: %s" Loc.report_line (symbol_start ()) s

  let add_pre_loc lb = function
    | Some (b,_) -> Loc.join (b,0) lb 
    | _ -> lb

  let expr_of_statement = function
    | CSnop l -> CEnop l
    | CSexpr (_, e) -> e
    | _ -> assert false

  (* used only for parsing types *)

  type specifier = 
    | Stypedef 
    | Sstorage of storage_class
    | Stype of ctype_expr
    | Sconst
    | Svolatile
    | Ssigned of bool (* true = signed / false = unsigned *)
    | Sstruct_named of string
    | Sstruct_decl of string option * parameters 
    | Sunion_named of string
    | Sunion_decl of string option * parameters
    | Senum_named of string
    | Senum_decl of string option * (string * cexpr option) list
	
  and specifiers = specifier list

  and declarator =
    | Dsimple
    | Dpointer of declarator
    | Darray of declarator * cexpr option
    | Dfunction of declarator * parameters * annot option
    | Dbitfield of declarator * cexpr

  and parameters = (specifiers * declarator * string) list

  (* interps a list of specifiers / declarators as a [ctype] *)

  let interp_type specs d = 
    failwith "todo"

  let interp_param (s, d, id) = interp_type s d, id
  let interp_params = List.map interp_param

  let is_typedef = List.exists ((=) Stypedef)

  let declaration specs decls =
    let l = loc() in
    if is_typedef specs then
      let interp = function
	| (n,d), Inothing -> Ctypes.add n; Ctypedef (l, interp_type specs d, n)
	| (n,_), _ -> error ("typedef " ^ n ^ " is initialized")
      in
      List.map interp decls
    else
      let interp ((n,d),i) =
	Ctypes.remove n; Cdecl (l, interp_type specs d, n, i)
      in
      List.map interp decls

%}

%token <int * string> ANNOT
%token <int * string> WDECL

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
        : IDENTIFIER { CEvar (loc (), $1) }
        | CONSTANT { CEconstant (loc (), $1) }
        | STRING_LITERAL { CEstring_literal (loc (), $1) }
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
	    { CEdot (loc (), $1, $3) }
        | postfix_expression PTR_OP IDENTIFIER 
	    { CEarrow (loc (), $1, $3) }
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
        | unary_operator cast_expression { CEunary (loc (), $1, $2) }
        | SIZEOF unary_expression { CEsizeof_expr (loc (), $2) }
        | SIZEOF LPAR type_name RPAR 
	    { let s,d = $3 in CEsizeof (loc (), interp_type s d) }
        ;

unary_operator
        : AMP { Uamp }
        | STAR { Ustar }
        | PLUS { Uplus }
        | MINUS { Uminus }
        | TILDE { Utilde }
        | EXL { Not }
        ;

cast_expression
        : unary_expression { $1 }
        | LPAR type_name RPAR cast_expression 
	    { let s,d = $2 in CEcast (loc (), interp_type s d, $4) }
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
        | shift_expression LEFT_OP additive_expression 
	    { CEshift (loc (), $1, Left, $3) }
        | shift_expression RIGHT_OP additive_expression 
	    { CEshift (loc (), $1, Right, $3) }
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
        : declaration_specifiers SEMICOLON 
            { warning "empty declaration"; [] }
        | declaration_specifiers init_declarator_list SEMICOLON 
	    { declaration $1 $2 }
	| WDECL  /* ADDED FOR WHY */
	    { [Cspecdecl $1] }
        ;

declaration_specifiers
        : storage_class_specifier { [$1] }
        | storage_class_specifier declaration_specifiers { $1 :: $2 }
        | type_specifier { [$1] }
        | type_specifier declaration_specifiers { $1 :: $2 }
        | type_qualifier { [$1] }
        | type_qualifier declaration_specifiers { $1 :: $2 }
        ;

init_declarator_list
        : init_declarator { [$1] }
        | init_declarator_list COMMA init_declarator { $1 @ [$3] }
        ;

init_declarator
        : declarator 
            { $1, Inothing }
        | declarator EQUAL c_initializer 
	    { $1, $3 }
        ;

storage_class_specifier
        : TYPEDEF { Stypedef }
        | EXTERN { Sstorage Extern }
        | STATIC { Sstorage Static }
        | AUTO { Sstorage Auto }
        | REGISTER { Sstorage Register }
        ;

type_specifier
        : VOID { Stype CTvoid }
        | CHAR { Stype CTchar }
        | SHORT { Stype CTshort }
        | INT { Stype CTint }
        | LONG { Stype CTlong }
        | FLOAT { Stype CTfloat }
        | DOUBLE { Stype CTdouble }
        | SIGNED { Ssigned true }
        | UNSIGNED { Ssigned false }
        | struct_or_union_specifier { $1 }
        | enum_specifier { $1 }
        | TYPE_NAME { Stype (CTvar $1) }
        ;

struct_or_union_specifier
        : struct_or_union IDENTIFIER LBRACE struct_declaration_list RBRACE 
            { if $1 then 
		Sstruct_decl (Some $2, $4) 
	      else 
		Sunion_decl (Some $2, $4) }
        | struct_or_union LBRACE struct_declaration_list RBRACE 
	    { if $1 then Sstruct_decl (None, $3) else Sunion_decl (None, $3) }
        | struct_or_union IDENTIFIER 
	    { if $1 then Sstruct_named $2 else Sunion_named $2 }
        ;

struct_or_union
        : STRUCT { true }
        | UNION { false }
        ;

struct_declaration_list
        : struct_declaration { $1 }
        | struct_declaration_list struct_declaration { $1 @ $2 }
        ;

struct_declaration
        : specifier_qualifier_list struct_declarator_list SEMICOLON 
            { let s = $1 in List.map (fun (id,d) -> s,d,id) $2 }
        ;

specifier_qualifier_list
        : type_specifier specifier_qualifier_list { $1 :: $2 }
        | type_specifier { [$1] }
        | type_qualifier specifier_qualifier_list { $1 :: $2 }
        | type_qualifier { [$1] }
        ;

struct_declarator_list
        : struct_declarator { [$1] }
        | struct_declarator_list COMMA struct_declarator { $1 @ [$3] }
        ;

struct_declarator
        : declarator 
            { $1 }
        | COLON constant_expression 
	    { "_", Dbitfield (Dsimple, $2) }
        | declarator COLON constant_expression 
	    { let x,d = $1 in x, Dbitfield (d, $3) }
        ;

enum_specifier
        : ENUM LBRACE enumerator_list RBRACE 
            { Senum_decl (None, $3) }
        | ENUM IDENTIFIER LBRACE enumerator_list RBRACE 
	    { Senum_decl (Some $2, $4) }
        | ENUM IDENTIFIER 
	    { Senum_named $2 }
        ;

enumerator_list
        : enumerator { [$1] }
        | enumerator_list COMMA enumerator { $1 @ [$3] }
        ;

enumerator
        : IDENTIFIER { $1, None }
        | IDENTIFIER EQUAL constant_expression { $1, Some $3 }
        ;

type_qualifier
        : CONST { Sconst }
        | VOLATILE { Svolatile }
        ;

declarator
        : pointer direct_declarator { let id,d = $2 in id, $1 d }
        | direct_declarator { $1 }
        ;

direct_declarator
        : IDENTIFIER 
            { $1, Dsimple }
        | LPAR declarator RPAR 
	    { uns() }
        | direct_declarator LSQUARE constant_expression RSQUARE 
	    { let id,d = $1 in id, Darray (d, Some $3) }
        | direct_declarator LSQUARE RSQUARE 
	    { let id,d = $1 in id, Darray (d, None) }
        | direct_declarator LPAR parameter_type_list RPAR annot 
	    { let id,d = $1 in id, Dfunction (d, $3, $5) }
        | direct_declarator LPAR identifier_list RPAR 
	    { uns() }
        | direct_declarator LPAR RPAR annot 
            { let id,d = $1 in id, Dfunction (d, [], $4) }
        ;

/* ADDED FOR WHY */
annot
        : ANNOT         { Some $1 }
        | /* epsilon */ { None }
        ;

pointer
        : STAR { fun d -> Dpointer d }
        | STAR type_qualifier_list { uns () }
        | STAR pointer { fun d -> Dpointer ($2 d) }
        | STAR type_qualifier_list pointer { uns () }
        ;

type_qualifier_list
        : type_qualifier { [$1] }
        | type_qualifier_list type_qualifier { $1 @ [$2] }
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
            { let id,d = $2 in $1, d, id }
        | declaration_specifiers abstract_declarator 
	    { $1, $2, "_" }
        | declaration_specifiers 
	    { ($1, Dsimple, "_") }
        ;

identifier_list
        : IDENTIFIER { }
        | identifier_list COMMA IDENTIFIER { }
        ;

type_name
        : specifier_qualifier_list { $1, Dsimple }
        | specifier_qualifier_list abstract_declarator { $1, $2 }
        ;

abstract_declarator
        : pointer { $1 Dsimple }
        | direct_abstract_declarator { $1 }
        | pointer direct_abstract_declarator { $1 $2 }
        ;

direct_abstract_declarator
        : LPAR abstract_declarator RPAR 
            { uns () }
        | LSQUARE RSQUARE 
	    { Darray (Dsimple, None) }
        | LSQUARE constant_expression RSQUARE 
	    { Darray (Dsimple, Some $2) }
        | direct_abstract_declarator LSQUARE RSQUARE 
	    { Darray ($1, None) }
        | direct_abstract_declarator LSQUARE constant_expression RSQUARE 
	    { Darray ($1, Some $3) }
        | LPAR RPAR 
	    { Dfunction (Dsimple, [], None) }
        | LPAR parameter_type_list RPAR 
	    { Dfunction (Dsimple, $2, None) }
        | direct_abstract_declarator LPAR RPAR 
	    { Dfunction ($1, [], None) }
        | direct_abstract_declarator LPAR parameter_type_list RPAR 
	    { Dfunction ($1, $3, None) }
        ;

c_initializer
        : assignment_expression { Iexpr $1 }
        | LBRACE c_initializer_list RBRACE { Ilist $2 }
        | LBRACE c_initializer_list COMMA RBRACE { Ilist $2 }
        ;

c_initializer_list
        : c_initializer { [$1] }
        | c_initializer_list COMMA c_initializer { $1 @ [$3] }
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
        : IDENTIFIER COLON statement { CSlabel (loc (), $1, $3) }
        | CASE constant_expression COLON statement { CScase (loc (), $2, $4) }
        | DEFAULT COLON statement { CSdefault (loc (), $3) }
        ;

compound_statement
        : compound_statement_LBRACE RBRACE 
            { Ctypes.pop (); [], [] }
        | compound_statement_LBRACE statement_list RBRACE 
	    { Ctypes.pop (); [], $2 }
        | compound_statement_LBRACE declaration_list RBRACE 
	    { Ctypes.pop (); $2, [] }
        | compound_statement_LBRACE declaration_list statement_list RBRACE 
	    { Ctypes.pop (); $2, $3 }
        ;

compound_statement_LBRACE:
  LBRACE { Ctypes.push () }
;

/* ADDED FOR WHY */
compound_statement_with_post
        : compound_statement annot { (loc (), $1, $2) }
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
	| ANNOT SEMICOLON { CSannot (loc (), $1) } /* ADDED FOR WHY */
        | expression SEMICOLON { CSexpr (loc (), $1) }
        ;

selection_statement
        : IF LPAR expression RPAR statement 
            { CScond (loc (), $3, $5, CSnop (loc ())) }
        | IF LPAR expression RPAR statement ELSE statement 
	    { CScond (loc (), $3, $5, $7) }
        | SWITCH LPAR expression RPAR statement 
	    { CSswitch (loc (), $3, $5) }
        ;

iteration_statement
        : WHILE LPAR expression RPAR ANNOT statement 
            { CSwhile (loc (), $3, $5, $6) }
        | DO statement ANNOT WHILE LPAR expression RPAR SEMICOLON 
	    { CSdowhile (loc (), $2, $3, $6) }
        | FOR LPAR expression_statement expression_statement RPAR ANNOT statement 
	    { CSfor (loc (), expr_of_statement $3, expr_of_statement $4, 
		     None, $6, $7) }
        | FOR LPAR expression_statement expression_statement expression RPAR ANNOT statement 
	    { CSfor (loc (), expr_of_statement $3, expr_of_statement $4, 
		     Some $5, $7, $8) }
        ;

jump_statement
        : GOTO IDENTIFIER SEMICOLON { CSgoto (loc (), $2) }
        | CONTINUE SEMICOLON { CScontinue (loc ()) }
        | BREAK SEMICOLON { CSbreak (loc ()) }
        | RETURN SEMICOLON { CSreturn (loc (), None) }
        | RETURN expression SEMICOLON { CSreturn (loc (), Some $2) }
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
            { let lb,b,q = loc_i 4, $4, None in
	      match $2 with
		| id, Dfunction (d, pl, p) ->
		    let lb = add_pre_loc lb p in
		    let ty = interp_type $1 d in
		    Cfundef (loc (), ty, id, interp_params pl, (lb,p,b,q))
		| _ -> uns () }
        | declaration_specifiers declarator compound_statement_with_post
	    { let (lb,b,q) = $3 in
              match $2 with
		| id, Dfunction (d, pl, p) -> 
		    let lb = add_pre_loc lb p in
		    let ty = interp_type $1 d in
		    Cfundef (loc (), ty, id, interp_params pl, (lb,p,b,q))
		| _ -> uns () }
        | declarator declaration_list compound_statement 
	    { uns () }
        | declarator compound_statement 
	    { uns () }
        ;

%%

(* C annotations *)

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

