
%{
  open Mix_ast
  open Parsing
%}

/* Tokens */ 

%token <string> IDENT
%token <string> STRING
%token <string> LABEL
%token AND EXISTS FALSE FORALL NOT OR TRUE
%token JUMP JCOND HALT

/* Precedences */

%right OR 
%right AND
%right NOT
/* Entry points */

%type <Mix_ast.file> file
%start file

%%

file:
| list1_stmt EOF 
   { List.rev $1 }
| EOF 
   { [] }
;

list1_stmt:
| stmt
   { [$1] }
| list1_stmt stmt
   { $2 :: $1 }
;

stmt:
| opt_label stmt_kind { $1, $2 }
;

stmt_kind:
| LBRALBRA STRING RBRARBRA { PSinvariant $3 }
| JUMP IDENT { PSjump $2 }
| JCOND IDENT { PScond $2 }
| HALT { PShalt }
| STRING { PSother $1 }
;

opt_label:
| LABEL         { Some $1 }
| /* epsilon */ { None }
;
