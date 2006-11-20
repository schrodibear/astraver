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

