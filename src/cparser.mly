/* from http://www.lysator.liu.se/c/ANSI-C-grammar-y.html */

%{

  open Logic
  open Ptree
  open Cast
  open Parsing

  let loc () = (symbol_start (), symbol_end ())

  let uns () =
    raise (Stdpp.Exc_located (loc (), Stream.Error "Unsupported C syntax"))

%}

%token <string> IDENTIFIER CONSTANT STRING_LITERAL ANNOT TYPE_NAME
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
        : IDENTIFIER { }
        | CONSTANT { }
        | STRING_LITERAL { }
        | LPAR expression RPAR { }
        ;

postfix_expression
        : primary_expression { }
        | postfix_expression LSQUARE expression RSQUARE { }
        | postfix_expression LPAR RPAR { }
        | postfix_expression LPAR argument_expression_list RPAR { }
        | postfix_expression DOT IDENTIFIER { }
        | postfix_expression PTR_OP IDENTIFIER { }
        | postfix_expression INC_OP { }
        | postfix_expression DEC_OP { }
        ;

argument_expression_list
        : assignment_expression { }
        | argument_expression_list COMMA assignment_expression { }
        ;

unary_expression
        : postfix_expression { }
        | INC_OP unary_expression { }
        | DEC_OP unary_expression { }
        | unary_operator cast_expression { }
        | SIZEOF unary_expression { }
        | SIZEOF LPAR type_name RPAR { }
        ;

unary_operator
        : AMP { }
        | STAR { }
        | PLUS { }
        | MINUS { }
        | TILDE { }
        | EXL { }
        ;

cast_expression
        : unary_expression { }
        | LPAR type_name RPAR cast_expression { }
        ;

multiplicative_expression
        : cast_expression { }
        | multiplicative_expression STAR cast_expression { }
        | multiplicative_expression SLASH cast_expression { }
        | multiplicative_expression PERCENT cast_expression { }
        ;

additive_expression
        : multiplicative_expression { }
        | additive_expression PLUS multiplicative_expression { }
        | additive_expression MINUS multiplicative_expression { }
        ;

shift_expression
        : additive_expression { }
        | shift_expression LEFT_OP additive_expression { }
        | shift_expression RIGHT_OP additive_expression { }
        ;

relational_expression
        : shift_expression { }
        | relational_expression LT shift_expression { }
        | relational_expression GT shift_expression { }
        | relational_expression LE_OP shift_expression { }
        | relational_expression GE_OP shift_expression { }
        ;

equality_expression
        : relational_expression { }
        | equality_expression EQ_OP relational_expression { }
        | equality_expression NE_OP relational_expression { }
        ;

and_expression
        : equality_expression { }
        | and_expression AMP equality_expression { }
        ;

exclusive_or_expression
        : and_expression { }
        | exclusive_or_expression HAT and_expression { }
        ;

inclusive_or_expression
        : exclusive_or_expression { }
        | inclusive_or_expression PIPE exclusive_or_expression { }
        ;

logical_and_expression
        : inclusive_or_expression { }
        | logical_and_expression AND_OP inclusive_or_expression { }
        ;

logical_or_expression
        : logical_and_expression { }
        | logical_or_expression OR_OP logical_and_expression { }
        ;

conditional_expression
        : logical_or_expression { }
        | logical_or_expression QUESTION expression COLON conditional_expression { }
        ;

assignment_expression
        : conditional_expression { }
        | unary_expression assignment_operator assignment_expression { }
        ;

assignment_operator
        : EQUAL { }
        | MUL_ASSIGN { }
        | DIV_ASSIGN { }
        | MOD_ASSIGN { }
        | ADD_ASSIGN { }
        | SUB_ASSIGN { }
        | LEFT_ASSIGN { }
        | RIGHT_ASSIGN { }
        | AND_ASSIGN { }
        | XOR_ASSIGN { }
        | OR_ASSIGN { }
        ;

expression
        : assignment_expression { }
        | expression COMMA assignment_expression { }
        ;

constant_expression
        : conditional_expression { }
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
        : labeled_statement { }
        | compound_statement { }
        | expression_statement { }
        | selection_statement { }
        | iteration_statement { }
        | jump_statement { }
        ;

labeled_statement
        : IDENTIFIER COLON statement { }
        | CASE constant_expression COLON statement { }
        | DEFAULT COLON statement { }
        ;

compound_statement
        : LBRACE RBRACE { }
        | LBRACE statement_list RBRACE { }
        | LBRACE declaration_list RBRACE { }
        | LBRACE declaration_list statement_list RBRACE { }
        ;

declaration_list
        : declaration { }
        | declaration_list declaration { }
        ;

statement_list
        : statement { }
        | statement_list statement { }
        ;

expression_statement
        : SEMICOLON { }
        | expression SEMICOLON { }
        ;

selection_statement
        : IF LPAR expression RPAR statement { }
        | IF LPAR expression RPAR statement ELSE statement { }
        | SWITCH LPAR expression RPAR statement { }
        ;

iteration_statement
        : WHILE LPAR expression RPAR statement { }
        | DO statement WHILE LPAR expression RPAR SEMICOLON { }
        | FOR LPAR expression_statement expression_statement RPAR statement { }
        | FOR LPAR expression_statement expression_statement expression RPAR statement { }
        ;

jump_statement
        : GOTO IDENTIFIER SEMICOLON { }
        | CONTINUE SEMICOLON { }
        | BREAK SEMICOLON { }
        | RETURN SEMICOLON { }
        | RETURN expression SEMICOLON { }
        ;

translation_unit
        : external_declaration { $1 }
        | translation_unit external_declaration { $1 @ $2 }
        ;

external_declaration
        : function_definition { uns() }
        | declaration { $1 }
        ;

function_definition
        : declaration_specifiers declarator declaration_list compound_statement { }
        | declaration_specifiers declarator compound_statement { }
        | declarator declaration_list compound_statement { }
        | declarator compound_statement { }
        ;

%%
