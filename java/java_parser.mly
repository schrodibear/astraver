/*

Parser for Java source files

$Id: java_parser.mly,v 1.15 2007-07-02 07:52:03 marche Exp $

*/


%{
  
  open Loc
  open Java_env
  open Java_ast

  let loc () = (symbol_start_pos (), symbol_end_pos ())

  let locate_expr e =
    { java_pexpr_node = e ; java_pexpr_loc = loc () }

  let locate_lit e = locate_expr (JPElit e)

  let locate_statement s =
    { java_pstatement_node = s ; java_pstatement_loc = loc () }

  let rec build_array_type t n =
    if n=0 then t else Array_type_expr(build_array_type t (pred n))

  let rec build_array_creation_expr t (l,n) =
    match l with
      | [] -> 
	  Implicit_array_creation(build_array_type t n)
      | a::b ->
	  Explicit_array_creation(a,(build_array_creation_expr t (b,n)))

%}

/*s Start symbols */

%start compilation_unit
%type  <Java_ast.compilation_unit> compilation_unit

%start kml_type_decl
%type  <Java_ast.type_declaration> kml_type_decl

%start kml_field_decl
%type  <Java_ast.field_declaration> kml_field_decl

%start kml_statement_annot
%type  <Java_ast.pstatement_node> kml_statement_annot

%type <Java_ast.qualified_ident> name

/*s Tokens */

/* Literals */

%token <string> ID 
%token <string> INTCONSTANT
%token <string> REALCONSTANT
%token <string> STRING
%token <string> CHARACTER
%token TRUE FALSE NULL THIS 

/* Keywords */

%token NEW SUPER
%token ABSTRACT BOOLEAN BYTE BYVALUE CASE CAST CATCH
%token CHAR CLASS CONST DEFAULT DOUBLE ELSE EXTENDS
%token FALSE FINAL FINALLY FLOAT FUTURE GENERIC GHOST GOTO 
%token IMPLEMENTS IMPORT INNER INSTANCEOF INT INTEGER INTERFACE LONG
%token NATIVE OPERATOR OUTER PACKAGE PRIVATE PROTECTED
%token PUBLIC REST REAL SHORT STATIC 
%token THROWS TRANSIENT TRUE VAR VOID VOLATILE
%token WHILE DO FOR IF SWITCH BREAK CONTINUE RETURN TRY SYNCHRONIZED THROW 

%token REQUIRES ENSURES SIGNALS ASSUMES ASSIGNS BEHAVIOR ASSERT
%token INVARIANT LOOP_INVARIANT DECREASES
%token AXIOM LOGIC TYPE PREDICATE READS
%token BSFORALL BSEXISTS BSOLD BSRESULT BSNOTHING

/* Others symbols */

%token LEFTPAR 
%token RIGHTPAR LEFTBRACE RIGHTBRACE LEFTBRACKET RIGHTBRACKET
%token SEMICOLON COLON COMMA QUESTIONMARK DOT DOTDOT
%token <string> DOC_COMMENT
%token <Lexing.position*string> ANNOT
%token EOF

/* Operators (see precedences below for details) */

%token <Java_ast.bin_op> ASSIGNOP
%token EQ EQEQGT LTEQEQGT
%token VERTICALBARVERTICALBAR
%token AMPERSANDAMPERSAND  
%token VERTICALBAR         
%token CARET               
%token AMPERSAND           
%token <Java_ast.bin_op> EQOP
%token <Java_ast.bin_op> COMP 
%token <Java_ast.bin_op> SHIFT
%token PLUS MINUS 
%token STAR SLASH PERCENT
%token PLUSPLUS MINUSMINUS TILDA BANG

/*s Operator precedences */

%nonassoc THEN
%nonassoc ELSE
%nonassoc BSFORALL
%right LTEQEQGT 
%right EQEQGT 
x%right EQ ASSIGNOP 
  /*r ["="], ["*="],  ["/="], ["%="], ["+="], ["-="], ["<<="], [">>="], 
  [">>>="], ["&="], ["^="] and ["|="], and ["==>"] ["<==>"] */ 
%right IFEXPR QUESTIONMARK     /*r [" ? : "] */
%left VERTICALBARVERTICALBAR  /*r conditional OR ["||"] */
%left AMPERSANDAMPERSAND  /*r conditional AND ["&&"] */
%left VERTICALBAR         /*r bitwise or boolean OR ["|"] */
%left CARET               /*r bitwise or boolean XOR ["^"] */
%left AMPERSAND           /*r bitwise or boolean AND ["&"] */
%left EQOP                /*r ["=="] and ["!="] */
%left COMP INSTANCEOF  /*r ["<"], ["<="], [">"], [">="] and ["instanceof"] */
%left SHIFT                 /*r ["<<"], [">>"] and [">>>"] */
%left PLUS MINUS             /*r ["+"] and ["-"] */
%left STAR SLASH PERCENT     /*r ["*"], ["/"] and ["%"] */
%right UMINUS UPLUS PLUSPLUS MINUSMINUS TILDA BANG CAST
           /*r unary ["+"], ["-"], ["++"], ["--"], ["~"], ["!"] and cast */


%%

/*s Compilation units */

compilation_unit:
| package_declaration import_declarations type_declarations EOF
    { { cu_package = $1 ;
	cu_imports = $2 ;
	cu_type_decls = $3} }
;

package_declaration:
| /* $\varepsilon$ */
    { [] }
| PACKAGE name SEMICOLON
    { $2 }
;

import_declarations:
| /* $\varepsilon$ */
    { [] }
| IMPORT import_declaration SEMICOLON import_declarations 
    { $2::$4 }
;


import_declaration:
| name DOT STAR 
    { Import_package($1) }
| name 
    { Import_class_or_interface($1) }
;

/*s type declarations */

type_declarations:
| /* $\varepsilon$ */
    { [] }
| type_declaration type_declarations
    { $1::$2 }
|  SEMICOLON type_declarations
    { $2 }
;

type_declaration:
| class_declaration 
    { JPTclass($1) }
| interface_declaration
    { JPTinterface($1) }
| ANNOT
    { let (loc,s) = $1 in JPTannot(loc,s) } 
;

/*s Class declarations */

class_declaration:
| modifiers CLASS ident extends_decl implements_decl 
    LEFTBRACE field_declarations RIGHTBRACE
    { { class_modifiers = $1;
	class_name = $3;
	class_extends = $4;
	class_implements = $5;
	class_fields = $7 }}
;

extends_decl:
| /* $\varepsilon$ */
    { None }
| EXTENDS name 
    { Some $2 }
;

implements_decl:
| /* $\varepsilon$ */
    { [] }
| IMPLEMENTS name_comma_list 
    { $2 }
;

field_declarations:
| /* $\varepsilon$ */
    { [] }
| field_declaration field_declarations
    { $1::$2 }
;

field_declaration:
| method_declaration 
    { $1 }
| constructor_declaration 
    { $1 }
| variable_declaration 
    { JPFvariable($1) }
| static_initializer 
    { JPFstatic_initializer($1) }
| ANNOT
    { let (loc,s)=$1 in JPFannot(loc,s) }
;

/*s variable declarations */

variable_declaration:
| modifiers_type_expr variable_declarators SEMICOLON
    { let (a,b)=$1 in
      match b with
	| Some b ->
	    { variable_modifiers = a ;
	      variable_type = b ;
	      variable_decls = $2 } 
	| None -> raise Parse_error} 
;

variable_declarators:
| variable_declarator
    { [$1] }
| variable_declarator COMMA variable_declarators
    { $1::$3 }
;

variable_declarator:
| variable_declarator_id 
    { { variable_id = $1 ;
	variable_initializer = None } }
| variable_declarator_id EQ variable_initializer
    { { variable_id = $1 ;
	variable_initializer = Some $3 } }
;

variable_declarator_id:
| ident
    { let (loc,id)=$1 in Simple_id(loc,id) }
| variable_declarator_id LEFTBRACKET RIGHTBRACKET
    { Array_id($1) } 

variable_initializer:
| expr
    { Simple_initializer($1) }
| LEFTBRACE variable_initializers RIGHTBRACE
    { Array_initializer($2) }
;

variable_initializers:
| /* $\varepsilon$ */
    { [] }
| variable_initializer 
    { [$1] }
| variable_initializer COMMA variable_initializers
    { $1::$3 }
; 


/*s static initializers */

static_initializer:
| STATIC block 
    { $2 }
;


/*s method declarations */

method_declaration:
| method_header method_body 
    { JPFmethod($1,$2) }
;

method_header:
| modifiers_type_expr method_declarator throws_decl
    { let (a,b)=$1 in
      { 
	method_modifiers = a ;
	method_return_type = b ;
	method_declarator = $2 ;
	method_throws = $3 
      } 
    }
;

method_declarator:
| ident method_parameters 
    { Simple_method_declarator($1,$2) }
| method_declarator LEFTBRACKET RIGHTBRACKET
    { Array_method_declarator($1) }
;


method_parameters:
| LEFTPAR RIGHTPAR 
    { [] }
| LEFTPAR parameter_comma_list RIGHTPAR
    { $2 }
;

parameter_comma_list:
| parameter
    { [$1] }
| parameter COMMA parameter_comma_list
    { $1::$3 }
;

parameter:
| type_expr ident 
    { Simple_parameter($1,$2) }
| parameter LEFTBRACKET RIGHTBRACKET
    { Array_parameter($1) }

throws_decl:
| /* $\varepsilon$ */
    { [] }
| THROWS name_comma_list
    { $2 }
;

method_body:
| block 
    { Some($1) } 
| SEMICOLON
    { None }
;

/*s constructor declarations */

constructor_declaration:
| modifiers_type_expr method_parameters throws_decl constructor_body
    { let (a,b)=$1 in
      match b with
	| Some (Type_name [id]) ->
	    let c =
	      { 
	      constr_modifiers = a ;
	      constr_name = id ;
	      constr_parameters = $2 ;
	      constr_throws = $3 }
	    in
	    let eci,b = $4 in
	    JPFconstructor(c,eci,b) 
	| _ -> raise Parse_error}
;

constructor_body:
| LEFTBRACE explicit_constructor_invocation statements RIGHTBRACE   
    { ($2,$3) }
| LEFTBRACE statements RIGHTBRACE   
    { (Invoke_none,$2) }
| SEMICOLON
    { (Invoke_none,[]) }
;

explicit_constructor_invocation:
| THIS LEFTPAR argument_list RIGHTPAR SEMICOLON
    { Invoke_this($3) }
| SUPER LEFTPAR argument_list RIGHTPAR SEMICOLON
    { Invoke_super($3) }
;

argument_list:
| /* $\varepsilon$ */
    { [] }
| expr_comma_list
    { $1 }
;

/*s interface declarations */

interface_declaration:
| modifiers INTERFACE ident extends_interfaces_decl 
    LEFTBRACE interface_member_declarations RIGHTBRACE
    { { interface_modifiers = $1;
	interface_name = $3;
	interface_extends = $4;
	interface_members = $6 }}
;

extends_interfaces_decl:
| /* $\varepsilon$ */
    { [] }
| EXTENDS name_comma_list 
    { $2 }
;

interface_member_declarations:
| /* $\varepsilon$ */
    { [] }
| interface_member_declaration interface_member_declarations
    { $1::$2 }
;

interface_member_declaration:
| variable_declaration
    { JPIMconstant($1) }
| method_header SEMICOLON
    { JPIMmethod($1) }
| ANNOT
    { let (loc,s)=$1 in JPIMannot(loc,s) }
;




/*s type expressions */

base_type:
| SHORT 
    { Tshort }
| BOOLEAN 
    { Tboolean }
| BYTE 
    { Tbyte }
| CHAR 
    { Tchar }
| INT 
    { Tint }
| FLOAT 
    { Tfloat }
| LONG 
    { Tlong }
| DOUBLE 
    { Tdouble }
| INTEGER
    { Tinteger }
| REAL
    { Treal }
;

type_expr:
| name 
    { Type_name($1) }
| base_type  
    { Base_type($1) }
| array_type_expr
    { Array_type_expr($1) }
;

array_type_expr:
| base_type LEFTBRACKET RIGHTBRACKET
    { Base_type($1) }
| name LEFTBRACKET RIGHTBRACKET
    { Type_name($1) }
| array_type_expr LEFTBRACKET RIGHTBRACKET
    { Array_type_expr($1) }
;


/*s modifiers */

modifiers:
| /* $\varepsilon$ */
    { [] }
| modifier modifiers
    { $1::$2 }
;
modifier:
| STATIC
    { `STATIC }
| FINAL
    { `FINAL }
| PUBLIC
    { `PUBLIC }
| PRIVATE 
    { `PRIVATE }
| PROTECTED
    { `PROTECTED }
| NATIVE
    { `NATIVE }
| SYNCHRONIZED
    { `SYNCHRONIZED }
| ABSTRACT
    { `ABSTRACT }
/* "threadsafe" ? */
| TRANSIENT
    { `TRANSIENT }
;

modifiers_type_expr:
| type_expr
    { ([],Some $1) }
| VOID
    { ([],None) }
| modifier modifiers_type_expr
    { let (a,b)=$2 in ($1::a,b) }
;

/*s Statements */

block:
| LEFTBRACE statements RIGHTBRACE   
    { $2 }

statements:
| statement statements
    { $1::$2 } 
| /* $\varepsilon$ */
    { [] } 
;

/*s Statements */

local_variable_declaration:
| modifiers_type_expr variable_declarators
    { let (a,b)=$1 in
      match b with
	| Some b ->
	    { variable_modifiers = a ;
	      variable_type = b ;
	      variable_decls = $2 }
	| None -> raise Parse_error } 
;

statement:
| WHILE LEFTPAR expr RIGHTPAR statement %prec WHILE
    { locate_statement (JPSwhile($3,$5)) }
| DO statement WHILE LEFTPAR expr RIGHTPAR 
    { locate_statement (JPSdo($2,$5)) } 
| FOR LEFTPAR argument_list SEMICOLON for_cond SEMICOLON 
  argument_list RIGHTPAR statement 
    { locate_statement (JPSfor($3,$5,$7,$9)) }
| FOR LEFTPAR local_variable_declaration SEMICOLON for_cond SEMICOLON 
  argument_list RIGHTPAR statement 
    { locate_statement (JPSfor_decl($3,$5,$7,$9)) }
| ANNOT
    { let (loc,s)=$1 in locate_statement (JPSannot(loc,s)) }
| expr SEMICOLON
    { locate_statement (JPSexpr($1)) }
| SEMICOLON
    { locate_statement JPSskip }
| local_variable_declaration SEMICOLON
    { locate_statement (JPSvar_decl($1)) }
| IF LEFTPAR expr RIGHTPAR statement %prec THEN
    { locate_statement (JPSif($3,$5,locate_statement JPSskip)) }
| IF LEFTPAR expr RIGHTPAR statement ELSE statement %prec ELSE
    { locate_statement (JPSif($3,$5,$7)) }
| SWITCH LEFTPAR expr RIGHTPAR LEFTBRACE switch_block RIGHTBRACE
    { locate_statement (JPSswitch($3,$6)) }
| block
    { locate_statement (JPSblock $1) }
| ident COLON statement
    { locate_statement (JPSlabel($1,$3)) } 
| BREAK SEMICOLON
    { locate_statement (JPSbreak None) }
| BREAK ident SEMICOLON
    { locate_statement (JPSbreak(Some $2)) }
| CONTINUE SEMICOLON
    { locate_statement (JPScontinue(None)) }
| CONTINUE ident SEMICOLON
    { locate_statement (JPScontinue(Some $2)) }
| RETURN SEMICOLON
    { locate_statement (JPSreturn None) }
| RETURN expr SEMICOLON
    { locate_statement (JPSreturn(Some $2)) }
| THROW expr SEMICOLON
    { locate_statement (JPSthrow($2)) }
| TRY block catch_clauses
    { locate_statement (JPStry($2,$3,None)) }
| TRY block catch_clauses FINALLY block
    { locate_statement (JPStry($2,$3,Some($5))) }
| TRY block FINALLY block
    { locate_statement (JPStry($2,[],Some($4))) }
| SYNCHRONIZED LEFTPAR expr RIGHTPAR block
    { locate_statement (JPSsynchronized($3,$5)) }

for_cond:
| expr
    { $1 }
| /* $\varepsilon$ */
    { locate_expr Java_pervasives.expr_node_true }
;

switch_block: 
| /* $\varepsilon$ */
    { [] }
| switch_labels 
    { [($1,[])] }
| switch_labels statement statements switch_block
    { ($1,$2::$3)::$4 }
;

switch_labels:
| switch_label
    { [$1] }
| switch_label switch_labels
    { $1::$2 }
;

switch_label:
| CASE expr COLON
    { Case($2) }
| DEFAULT COLON
    { Default }
;

catch_clauses:
| catch_clause
    { [$1] }
| catch_clause catch_clauses
    { $1::$2 }
;

catch_clause:
| CATCH LEFTPAR parameter RIGHTPAR block
    { ($3,$5) }
;

/*s Expressions */

field_access:
| SUPER DOT ident
    { Super_access $3 }
| primary_expr DOT ident
    { Primary_access($1,$3) }
;

primary_expr:
| primary_no_new_array
    { $1 }
| array_creation_expression
    { $1 }
;

primary_no_new_array:
| INTCONSTANT                    
    { locate_lit (Integer $1) }
| REALCONSTANT                    
    { locate_lit (Float $1) }
| TRUE                       
    { locate_lit (Bool true) }
| FALSE                      
    { locate_lit (Bool false) } 
| STRING                     
    { locate_lit (String $1) }
| NULL                     
    { locate_lit Null }
| CHARACTER                     
    { locate_lit (Char $1) }
| THIS
    { locate_expr JPEthis }
| BSRESULT
    { locate_expr JPEresult }
| LEFTPAR expr_no_name RIGHTPAR      
    { $2 }
| LEFTPAR name RIGHTPAR
    { locate_expr (JPEname $2) }
| field_access
    { locate_expr (JPEfield_access $1) }
| ident LEFTPAR argument_list RIGHTPAR
    { locate_expr (JPEcall(None,$1,$3)) } 
| name DOT ident LEFTPAR argument_list RIGHTPAR
    { let n = locate_expr (JPEname $1) in
      locate_expr (JPEcall(Some n,$3,$5)) } 
| SUPER DOT ident LEFTPAR argument_list RIGHTPAR
    { locate_expr (JPEsuper_call($3, $5)) }
| primary_expr DOT ident LEFTPAR argument_list RIGHTPAR
    { locate_expr (JPEcall(Some $1,$3,$5)) } 
| NEW name LEFTPAR argument_list RIGHTPAR
    { locate_expr (JPEnew($2,$4)) }
| array_access
    { let (a,b)=$1 in locate_expr (JPEarray_access(a,b)) }
| BSOLD LEFTPAR expr RIGHTPAR
    { locate_expr (JPEold $3) }
;

array_access:
| primary_no_new_array LEFTBRACKET expr RIGHTBRACKET
    { ($1,$3) }
| name LEFTBRACKET expr RIGHTBRACKET
    { (locate_expr (JPEname $1),$3) }
;

array_creation_expression:
| NEW base_type array_dims
    { locate_expr (JPEnew_array(build_array_creation_expr (Base_type($2)) $3)) }
| NEW name array_dims
    { locate_expr (JPEnew_array(build_array_creation_expr (Type_name($2)) $3)) }
;

array_dims:
| LEFTBRACKET expr RIGHTBRACKET implicit_dims
    { ([$2],$4) }
| LEFTBRACKET expr RIGHTBRACKET array_dims
    { let (a,b) = $4 in ($2::a,b) }
;

implicit_dims:
| /* $\varepsilon$$ */
    { 0 }
| LEFTBRACKET RIGHTBRACKET implicit_dims
    { succ $3 }
;

castable_expr:
| primary_expr
    { $1 }
| name
    { locate_expr (JPEname $1) }
| non_basic_cast
    { $1 }

non_basic_cast:
| LEFTPAR array_type_expr RIGHTPAR castable_expr %prec CAST
    { locate_expr (JPEcast(Array_type_expr($2),$4)) }
| LEFTPAR name RIGHTPAR castable_expr %prec CAST
    { locate_expr (JPEcast(Type_name($2),$4)) }
;

expr:
| name
    { locate_expr (JPEname $1) }
| expr_no_name
    { $1 }
;

expr_no_name:
| primary_expr
    { $1 }
| name assign_op expr %prec ASSIGNOP
    { locate_expr (JPEassign_name($1,$2,$3)) }
| field_access assign_op expr %prec ASSIGNOP
    { locate_expr (JPEassign_field($1,$2,$3)) }
| array_access assign_op expr %prec ASSIGNOP
    { let (a,b)=$1 in 
      locate_expr (JPEassign_array(a,b,$2,$3)) }
| PLUSPLUS expr 
    { locate_expr (JPEincr(Preincr,$2)) }
| MINUSMINUS expr 
    { locate_expr (JPEincr(Predecr,$2)) }
| expr PLUSPLUS 
    { locate_expr (JPEincr(Postincr,$1)) }
| expr MINUSMINUS 
    { locate_expr (JPEincr(Postdecr,$1)) }
| expr QUESTIONMARK expr COLON expr %prec IFEXPR
    { locate_expr (JPEif($1,$3,$5)) }
| expr VERTICALBARVERTICALBAR expr          
    { locate_expr (JPEbin($1,Bor,$3)) }
| expr AMPERSANDAMPERSAND expr          
    { locate_expr (JPEbin($1,Band,$3)) }
| expr VERTICALBAR expr          
    { locate_expr (JPEbin($1,Bbwor,$3)) }
| expr CARET expr          
    { locate_expr (JPEbin($1,Bbwxor,$3)) } 
| expr AMPERSAND expr          
    { locate_expr (JPEbin($1,Bbwand,$3)) } 
| expr EQOP expr          
    { locate_expr (JPEbin($1,$2,$3)) } 
| expr COMP expr         
    { locate_expr (JPEbin($1,$2,$3)) } 
| expr SHIFT expr         
    { locate_expr (JPEbin($1,$2,$3)) } 
| expr PLUS expr          
    { locate_expr (JPEbin($1,Badd,$3)) }  
| expr MINUS expr         
    { locate_expr (JPEbin($1,Bsub,$3)) }  
| expr STAR expr        
    { locate_expr (JPEbin($1,Bmul,$3)) } 
| expr SLASH expr       
    { locate_expr (JPEbin($1,Bdiv,$3)) }  
| expr PERCENT expr        
    { locate_expr (JPEbin($1,Bmod,$3)) }  
| PLUS expr %prec UPLUS 
    { locate_expr (JPEun(Uplus,$2)) }  
| MINUS expr %prec UMINUS 
    { locate_expr (JPEun(Uminus,$2)) }  
| BANG expr
    { locate_expr (JPEun(Unot,$2)) }  
| TILDA expr
    { locate_expr (JPEun(Ucompl,$2)) }  
/*

  CAST expressions

  we distinguish cast types because of syntax ambiguities:
  is (id1)-id2  a cast of a unary minus, or a binary - ?

  solution:
       
  if id1 is a base type, it is a cast else it is a binary operation. 
  it is enough because result of unary - cannot be casted to something 
  else than a base type.    

  moreover, we distinguish between cast to a type identifier 
  "(name) expr" and a complex type expr, because of LALR constraint:
  (name) can be both an expr and a cast, so it is factorized. 

*/
| LEFTPAR base_type RIGHTPAR expr %prec CAST
    { locate_expr (JPEcast(Base_type($2),$4)) }
| non_basic_cast
    { $1 }
/* 
  instanceof operator
*/
| expr INSTANCEOF type_expr
    { locate_expr (JPEinstanceof($1,$3)) }
/* annotations only operators */
| BSFORALL quantified_variables_decl SEMICOLON expr %prec BSFORALL
    { let (t,v)=$2 in
      locate_expr (JPEquantifier(Forall,t,v,$4)) }
| BSEXISTS quantified_variables_decl SEMICOLON expr %prec BSFORALL
    { let (t,v)=$2 in
      locate_expr (JPEquantifier(Exists,t,v,$4)) }
| expr EQEQGT expr
    { locate_expr (JPEbin($1,Bimpl,$3)) }
| expr LTEQEQGT expr
    { locate_expr (JPEbin($1,Biff,$3)) }
;

quantified_variables_decl:
| type_expr quantified_variables
    { ($1,$2) }
;

quantified_variables:
| quantified_variable
    { [$1] }
| quantified_variable COMMA quantified_variables
    { $1::$3 }
;

quantified_variable:
| ident
    { let (loc,id)=$1 in Simple_id(loc,id) }
| quantified_variable LEFTBRACKET RIGHTBRACKET
    { Array_id($1) } 


expr_comma_list:
| expr
    { [$1] }
| expr COMMA expr_comma_list
    { $1::$3 }
;

assign_op:
| EQ 
    { Beq }
| ASSIGNOP
    { $1 }
;

/*s identifiers */


name:
| ident
    { [$1] }
| name DOT ident
    { $3::$1 }
;

name_comma_list:
| name
    { [$1] }
| name COMMA name_comma_list
    { $1::$3 }
;

ident:
| ID
    { (loc(),$1) }
;

/****************************************************/
/*s parsing of annotations: KML */

kml_type_decl:
| PREDICATE ident method_parameters LEFTBRACE expr RIGHTBRACE EOF
    { JPTlogic_def($2,None,$3,$5) }
| LOGIC type_expr ident method_parameters LEFTBRACE expr RIGHTBRACE EOF
    { JPTlogic_def($3,Some $2,$4,$6) }
| LOGIC type_expr ident method_parameters READS expr_comma_list SEMICOLON EOF
    { JPTlogic_reads($3,Some $2,$4,$6) }
| AXIOM ident COLON expr SEMICOLON EOF
    { JPTaxiom($2,$4) }

kml_field_decl:
| requires behaviors EOF
    { JPFmethod_spec($1,$2) }
| INVARIANT ident COLON expr SEMICOLON EOF
    {  JPFinvariant($2,$4) } 
;

requires:
| /* $\varepsilon$ */
    { None }
| REQUIRES expr SEMICOLON
    { Some $2 }
;

behaviors:
| /* $\varepsilon$ */
    { [] }
| BEHAVIOR ident COLON behavior behaviors
    { ($2,$4)::$5 }
;

behavior:
| assumes assigns ENSURES expr SEMICOLON
    { { java_pbehavior_assumes = $1;
	java_pbehavior_assigns = $2;
	java_pbehavior_throws = None;
	java_pbehavior_ensures = $4 } }
| assumes assigns SIGNALS LEFTPAR name ident_option RIGHTPAR expr SEMICOLON
    { { java_pbehavior_assumes = $1;
	java_pbehavior_assigns = $2;
	java_pbehavior_throws = Some($5,$6);
	java_pbehavior_ensures = $8 } }
| error
	{ raise (Java_options.Java_error (loc(),"`ensures' expected")) }
;

ident_option:
| /* $\varepsilon$ */
    { None }
| ident
    { Some $1 }
;
 
assumes:
| /* $\varepsilon$ */
    { None }
| ASSUMES expr SEMICOLON
    { Some $2 }
;


assigns:
| /* $\varepsilon$ */
    { None }
| ASSIGNS BSNOTHING SEMICOLON
    { Some [] }
| ASSIGNS expr_comma_list SEMICOLON
    { Some $2 }
;

kml_statement_annot:
| LOOP_INVARIANT expr SEMICOLON DECREASES expr SEMICOLON EOF
    { JPSloop_annot($2,$5) }
| ASSERT expr SEMICOLON EOF
    { JPSassert(None,$2) }
| ASSERT ident COLON expr SEMICOLON EOF
    { JPSassert(Some $2,$4) }
| GHOST local_variable_declaration SEMICOLON EOF
    { JPSghost_local_decls($2) }
| GHOST expr SEMICOLON EOF
    { JPSghost_statement($2) }
;

/*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*/
