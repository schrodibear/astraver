%{
  open Simplify_ast
%}

%token <Simplify_ast.atom> ATOM
%token LPAR RPAR EOF

%type <Simplify_ast.t> start
%start start

%%

start: 
  list0_sexp EOF { $1 }
;

list0_sexp:
  /* epsilon */ { [] }
| list1_sexp    { $1 }
;

list1_sexp:
  sexp            { [$1] }
| sexp list1_sexp { $1 :: $2 }
;
 
sexp:
  ATOM                 { Satom $1 }
| LPAR list1_sexp RPAR { Slist $2 }
;

