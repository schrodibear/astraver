/* $Id */

%{

  open Format
  open Jc_env
  open Jc_ast
  open Parsing
  open Error

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)

(*
  let locate x = { node = x; loc = loc() }
  let locate_i i x = { node = x; loc = loc_i i }
  let with_loc l x = { node = x; loc = l }
*)

(*
  let error s = 
    Report.raise_located (loc ()) (AnyMessage ("Syntax error: " ^ s))
*)

%}

%token <string> IDENTIFIER STRING_LITERAL 
%token <Jc_ast.const> CONSTANT
%token PTR_OP INC_OP DEC_OP LEFT_OP RIGHT_OP LE_OP GE_OP EQ_OP NE_OP
%token AND_OP OR_OP MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN
%token SUB_ASSIGN LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN
%token XOR_ASSIGN OR_ASSIGN

%token TYPEDEF 
%token CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE VOID
%token STRUCT ENUM 

%token CASE DEFAULT IF ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN 
%token TRY CATCH FINALLY THROW

%token SEMICOLON LBRACE RBRACE COMMA COLON EQUAL LPAR RPAR LSQUARE RSQUARE
%token DOT AMP EXL TILDE MINUS PLUS STAR SLASH PERCENT LT GT HAT PIPE
%token QUESTION EOF


%type <Jc_ast.decl list> file
%start file
%%

file: 
| decl file 
    { $1::$2 }
| EOF 
    { [] }
;

/*
primary_expression: 
| IDENTIFIER 
    { locate (CEvar $1) }
| CONSTANT 
    { locate (CEconstant $1) }
| STRING_LITERAL 
    { locate (CEstring_literal $1) }
| LPAR expression RPAR { $2 }
;

postfix_expression: 
| primary_expression 
    { $1 }
| postfix_expression LPAR RPAR 
    { locate (CEcall ($1, [])) }
| postfix_expression LPAR argument_expression_list RPAR 
    { locate (CEcall ($1, $3)) }
| postfix_expression PTR_OP identifier
    { locate (CEarrow ($1, $3)) }
| postfix_expression INC_OP 
    { locate (CEincr (Upostfix_inc, $1)) }
| postfix_expression DEC_OP
    { locate (CEincr (Upostfix_dec, $1)) }
;

argument_expression_list: 
| assignment_expression 
    { [$1] }
| argument_expression COMMA assignment_expression_list 
    { $1::$3 }
;

unary_expression: 
| postfix_expression 
    { $1 }
| INC_OP unary_expression 
    { locate (CEincr (Uprefix_inc, $2)) }
| DEC_OP unary_expression 
    { locate (CEincr (Uprefix_dec, $2)) }
| unary_operator cast_expression 
    { locate (CEunary ($1, $2)) }
;

unary_operator: 
| PLUS 
    { Uplus }
| MINUS 
    { Uminus }
| TILDE 
    { Utilde }
| EXL 
    { Unot }
;

cast_expression: 
| unary_expression { $1 }
;

multiplicative_expression: 
| cast_expression 
    { $1 }
| multiplicative_expression STAR cast_expression 
    { locate (CEbinary ($1, Bmul, $3)) }
| multiplicative_expression SLASH cast_expression 
    { locate (CEbinary ($1, Bdiv, $3)) }
| multiplicative_expression PERCENT cast_expression 
    { locate (CEbinary ($1, Bmod, $3)) }
;

additive_expression: 
| multiplicative_expression 
    { $1 }
| additive_expression PLUS multiplicative_expression 
    { locate (CEbinary ($1, Badd, $3)) }
| additive_expression MINUS multiplicative_expression 
    { locate (CEbinary ($1, Bsub, $3)) }
;

shift_expression: 
| additive_expression 
    { $1 }
| shift_expression LEFT_OP additive_expression 
    { locate (CEbinary ($1, Bshift_left, $3)) }
| shift_expression RIGHT_OP additive_expression 
    { locate (CEbinary ($1, Bshift_right, $3)) }
;

relational_expression: 
| shift_expression 
    { $1 }
| relational_expression LT shift_expression 
    { locate (CEbinary ($1, Blt, $3)) }
| relational_expression GT shift_expression
    { locate (CEbinary ($1, Bgt, $3)) }
| relational_expression LE_OP shift_expression
    { locate (CEbinary ($1, Ble, $3)) }
| relational_expression GE_OP shift_expression
    { locate (CEbinary ($1, Bge, $3)) }
;

equality_expression: 
| relational_expression 
    { $1 }
| equality_expression EQ_OP relational_expression 
    { locate (CEbinary ($1, Beq, $3)) }
| equality_expression NE_OP relational_expression 
    { locate (CEbinary ($1, Bneq, $3)) }
;

and_expression: 
| equality_expression 
    { $1 }
| and_expression AMP equality_expression 
    { locate (CEbinary ($1, Bbw_and, $3)) }
;

exclusive_or_expression: 
| and_expression 
    { $1 }
| exclusive_or_expression HAT and_expression 
    { locate (CEbinary ($1, Bbw_xor, $3)) }
;

inclusive_or_expression: 
| exclusive_or_expression 
    { $1 }
| inclusive_or_expression PIPE exclusive_or_expression 
    { locate (CEbinary ($1, Bbw_or, $3)) }
;

logical_and_expression: 
| inclusive_or_expression 
    { $1 }
| logical_and_expression AND_OP inclusive_or_expression 
    { locate (CEbinary ($1, Band, $3)) }
;

logical_or_expression: 
| logical_and_expression 
    { $1 }
| logical_or_expression OR_OP logical_and_expression 
    { locate (CEbinary ($1, Bor, $3)) }
;

conditional_expression: 
| logical_or_expression 
    { $1 }
| logical_or_expression QUESTION expression COLON conditional_expression 
    { locate (CEcond ($1, $3, $5)) }
;

assignment_expression: 
| conditional_expression 
    { $1 }
| unary_expression assignment_operator assignment_expression 
    { locate (match $2 with
		| Aequal -> CEassign ($1, $3)
		| Amul -> CEassign_op ($1, Bmul, $3)
		| Adiv -> CEassign_op ($1, Bdiv, $3)
		| Amod -> CEassign_op ($1, Bmod, $3)
		| Aadd -> CEassign_op ($1, Badd, $3)
		| Asub -> CEassign_op ($1, Bsub, $3)
		| Aleft -> CEassign_op ($1, Bshift_left, $3)
		| Aright -> CEassign_op ($1, Bshift_right, $3)
		| Aand -> CEassign_op ($1, Bbw_and, $3)
		| Axor -> CEassign_op ($1, Bbw_xor, $3)
		| Aor -> CEassign_op ($1, Bbw_or, $3)) 
    }
;

assignment_operator: 
| EQUAL { Aequal }
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

expression: 
| assignment_expression 
    { $1 }
| expression COMMA assignment_expression { locate (CEseq ($1, $3)) }
;

constant_expression: 
| conditional_expression { $1 }
;

declaration: 
| declaration_specifiers SEMICOLON 
    { type_declarations $1 }
| declaration_specifiers init_declarator_list attributes_opt SEMICOLON 
    { List.map locate (declaration $1 $2) }
| SPEC declaration_specifiers init_declarator_list attributes_opt SEMICOLON 
    { [locate (spec_declaration $1 $2 $3)] }
| DECL  
    { List.map (fun d -> locate (Cspecdecl d)) $1 }
;

*/

/* the precedence specs indicates to keep going with declaration_specifiers */
/*
declaration_specifiers
        : storage_class_specifier %prec specs { [$1] }
        | storage_class_specifier declaration_specifiers { $1 :: $2 }
        | type_specifier { [$1] }
        | type_specifier declaration_specifiers_no_name { $1 :: $2 }
        | type_qualifier %prec specs { [$1] }
        | type_qualifier declaration_specifiers { $1 :: $2 }
        ;
*/
/* same thing, with TYPE_NAME no more allowed */
/*
declaration_specifiers_no_name
        : storage_class_specifier %prec specs { [$1] }
        | storage_class_specifier declaration_specifiers_no_name { $1 :: $2 }
        | type_specifier_no_name { [$1] }
        | type_specifier_no_name declaration_specifiers_no_name { $1 :: $2 }
        | type_qualifier %prec specs { [$1] }
        | type_qualifier declaration_specifiers { $1 :: $2 }
        ;

init_declarator_list
        : init_declarator { [$1] }
        | init_declarator_list COMMA init_declarator { $1 @ [$3] }
        ;

init_declarator
        : declarator 
            { $1, None }
        | declarator EQUAL c_initializer 
	    { $1, Some $3 }
        ;

storage_class_specifier
        : TYPEDEF { Stypedef }
        | EXTERN { Sstorage Extern }
        | STATIC { Sstorage Static }
        | AUTO { Sstorage Auto }
        | REGISTER { Sstorage Register }
        ;

type_specifier
        : type_specifier_no_name { $1 }
        | TYPE_NAME { Stype (CTvar $1) }
        ;
type_specifier_no_name
        : VOID { Stype CTvoid }
        | CHAR { Stype (CTint (Unsigned, Char)) }
        | SHORT { Sshort }
        | INT { Stype (CTint (Signed, Int)) }
        | LONG { Slong }
        | FLOAT { Stype (CTfloat Float) }
        | DOUBLE { Stype (CTfloat Double) }
        | SIGNED { Ssign Signed }
        | UNSIGNED { Ssign Unsigned }
        | struct_or_union_specifier { $1 }
        | enum_specifier { $1 }
        ;

identifier
        : IDENTIFIER { $1 }
        | TYPE_NAME  { $1 }
	;

struct_or_union_specifier
        : struct_or_union identifier LBRACE struct_declaration_list RBRACE 
            { if $1 then 
		Sstruct_decl (Some $2, $4) 
	      else 
		Sunion_decl (Some $2, $4) }
        | struct_or_union LBRACE struct_declaration_list RBRACE 
	    { if $1 then Sstruct_decl (None, $3) else Sunion_decl (None, $3) }
        | struct_or_union identifier 
	    { Stype (if $1 then CTstruct ($2, Tag) else CTunion ($2, Tag)) }
        ;

struct_declaration_list: 
	| struct_declaration { $1 }
        | struct_declaration_list struct_declaration { $1 @ $2 }
        ;

struct_declaration
        : specifier_qualifier_list struct_declarator_list SEMICOLON 
            { let s = $1 in List.map (fun ((id,d),bf) -> s,d,id,bf) $2 }
        ;

specifier_qualifier_list
        : type_specifier specifier_qualifier_list_no_name { $1 :: $2 }
        | type_specifier { [$1] }
        | type_qualifier specifier_qualifier_list { $1 :: $2 }
        | type_qualifier %prec specs { [$1] }
        ;
*/
/* same thing, with TYPE_NAME no more allowed */
/*
specifier_qualifier_list_no_name
        : type_specifier_no_name specifier_qualifier_list_no_name { $1 :: $2 }
        | type_specifier_no_name { [$1] }
        | type_qualifier specifier_qualifier_list_no_name { $1 :: $2 }
        | type_qualifier { [$1] }
        ;

struct_declarator_list
        : struct_declarator { [$1] }
        | struct_declarator_list COMMA struct_declarator { $1 @ [$3] }
        ;

struct_declarator
        : declarator 
            { $1, None }
        | COLON constant_expression 
	    { ("_", Dsimple), Some $2 }
        | declarator COLON constant_expression 
	    { $1, Some $3 }
        ;

enum_specifier
        : ENUM LBRACE enumerator_list RBRACE 
            { Stype (CTenum (fresh_name None, Decl $3)) }
        | ENUM identifier LBRACE enumerator_list RBRACE 
	    { Stype (CTenum ($2, Decl $4)) }
        | ENUM identifier 
	    { Stype (CTenum ($2, Tag)) }
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
	| RESTRICT { dwarning "ignored __restrict"; Srestrict }
        ;

declarator
        : pointer direct_declarator { let id,d = $2 in id, $1 d }
        | direct_declarator { $1 }
        ;

direct_declarator
        : identifier
            { $1, Dsimple }
        | LPAR declarator RPAR 
	    { $2 }
        | direct_declarator LSQUARE constant_expression RSQUARE 
	    { let id,d = $1 in id, Darray (d, Some $3) }
        | direct_declarator LSQUARE RSQUARE 
	    { let id,d = $1 in id, Darray (d, None) }
        | direct_declarator LPAR parameter_type_list RPAR
	    { let id,d = $1 in id, Dfunction (d, $3) }
        | direct_declarator LPAR identifier_list RPAR
	    { let pl = List.map (fun x -> ([], Dsimple, x)) $3 in
	      let id,d = $1 in id, Dfunction (d, pl) }
        | direct_declarator LPAR RPAR
            { let id,d = $1 in id, Dfunction (d, []) }
        ;

loop_annot
        : LOOP_ANNOT                   { $1 }
        ;

pointer
        : STAR { fun d -> Dpointer d }
        | STAR type_qualifier_list 
	    { dwarning "ignored qualifiers"; fun d -> Dpointer d }
        | STAR pointer { fun d -> Dpointer ($2 d) }
        | STAR type_qualifier_list pointer 
	    { dwarning "ignored qualifiers"; fun d -> Dpointer ($3 d) }
        ;

type_qualifier_list
        : type_qualifier { [$1] }
        | type_qualifier_list type_qualifier { $1 @ [$2] }
        ;


parameter_type_list
        : parameter_list { $1 }
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
        : IDENTIFIER { [$1] }
        | identifier_list COMMA IDENTIFIER { $1 @ [$3] }
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
            { $2 }
        | LSQUARE RSQUARE 
	    { Darray (Dsimple, None) }
        | LSQUARE constant_expression RSQUARE 
	    { Darray (Dsimple, Some $2) }
        | direct_abstract_declarator LSQUARE RSQUARE 
	    { Darray ($1, None) }
        | direct_abstract_declarator LSQUARE constant_expression RSQUARE 
	    { Darray ($1, Some $3) }
        | LPAR RPAR 
	    { Dfunction (Dsimple, []) }
        | LPAR parameter_type_list RPAR 
	    { Dfunction (Dsimple, $2) }
        | direct_abstract_declarator LPAR RPAR 
	    { Dfunction ($1, []) }
        | direct_abstract_declarator LPAR parameter_type_list RPAR 
	    { Dfunction ($1, $3) }
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
        | compound_statement { locate (CSblock $1) }
        | expression_statement { $1 }
        | selection_statement { $1 }
        | iteration_statement { $1 }
        | jump_statement { $1 }
	| SPEC statement { locate (CSspec ($1,$2)) }
        ;

labeled_statement
        : identifier COLON statement { locate (CSlabel ($1, $3)) }
        | CASE constant_expression COLON statement { locate (CScase ($2, $4)) }
        | DEFAULT COLON statement { locate (CSdefault($3)) }
        ;
*/

compound_statement:
| LBRACE RBRACE 
            { [] }
/*
        | compound_statement_LBRACE statement_list RBRACE 
	    { Ctypes.pop (); [], $2 }
        | compound_statement_LBRACE declaration_list RBRACE 
	    { Ctypes.pop (); $2, [] }
        | compound_statement_LBRACE declaration_list statement_list RBRACE 
	    { Ctypes.pop (); $2, $3 }
/*
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
        : SEMICOLON { locate CSnop }
	| CODE_ANNOT { locate (CSannot $1) } 
        | expression SEMICOLON { locate (CSexpr $1) }
        ;

selection_statement
        : IF LPAR expression RPAR statement 
            { locate (CSif ($3, $5, locate CSnop)) }
        | IF LPAR expression RPAR statement ELSE statement 
	    { locate (CSif ($3, $5, $7)) }
        | SWITCH LPAR expression RPAR statement 
	    { locate (CSswitch ($3, $5)) }
        ;

iteration_statement
        : loop_annot WHILE LPAR expression RPAR statement 
            { locate (CSwhile ($1, $4, $6)) }
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

jump_statement
        : GOTO identifier SEMICOLON { locate (CSgoto $2) }
        | CONTINUE SEMICOLON { locate CScontinue }
        | BREAK SEMICOLON { locate CSbreak }
        | RETURN SEMICOLON { locate (CSreturn None) }
        | RETURN expression SEMICOLON { locate (CSreturn (Some $2)) }
        ;

translation_unit
        : external_declaration { $1 }
        | translation_unit external_declaration { $1 @ $2 }
        ;

*/

decl: 
| function_definition { [$1] }
/*
| declaration { $1 }
*/
;

function_definition: 
| function_prototype compound_statement
    { let bl = locate_i 2 (JCSblock $2) in
      locate (JCDfun($1, bl)) }
;
	      
function_prototype:
| /*type_expr*/ IDENTIFIER LBRACE RBRACE { JCDfun({jc_fun_info_name = ""; jc_fun_info_return_type = JCTlogic "unit" },[],JCSskip) }
/*
        : declaration_specifiers declarator declaration_list 
            { Ctypes.push (); function_declaration $1 $2 $3 }
        | declaration_specifiers declarator 
	    { Ctypes.push (); function_declaration $1 $2 [] }
        | declarator declaration_list
	    { Ctypes.push (); function_declaration [] $1 $2 }
        | declarator
	    { Ctypes.push (); function_declaration [] $1 [] }

*/
;


