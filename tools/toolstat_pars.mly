/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-François COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLIÂTRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCHÉ                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann RÉGIS-GIANAS                                                   */
/*    Nicolas ROUSSET                                                     */
/*    Xavier URBAIN                                                       */
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

/* $Id: toolstat_pars.mly,v 1.1 2008-10-08 01:22:04 moy Exp $ */

%{
  open Format
  open Parsing
  open Toolstat_types
%}

%token < Toolstat_types.prover > PROVER
%token < Toolstat_types.test > TEST
%token < Toolstat_types.result > RESULT
%token < Toolstat_types.time > TIME 

%token EOF
%type < Toolstat_types.record list > log
%start log

%%

log: 
| record log 
    { $1::$2 }
| EOF 
    { [] }
;

record:
| PROVER TEST RESULT TIME
    { let summary,detail = $3 in ($1,$2,summary,detail,$4) }
;
