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
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2, with the special exception on linking              */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

/* $Id: toolstat_pars.mly,v 1.5 2008-11-05 14:03:19 filliatr Exp $ */

%{
  open Format
  open Parsing
  open Toolstat_types
    
  let default_test = let count = ref 0 in function () ->
    incr count; "Unknown" ^ (string_of_int !count)
  let default_summary = (0,0,0,0,0)
  let default_detail = ([],[],[],[],[])
  let default_time = (0,0,0.)
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
    { let summary,detail = $3 in (true,$1,$2,summary,detail,$4) }
| PROVER TEST RESULT
    { (* Case for no VC *)
      let summary,detail = $3 in (true,$1,$2,summary,detail,default_time) }
| PROVER TEST
    { (* Error case *)
      (false,$1,$2,default_summary,default_detail,default_time) }
| PROVER
    { (* Error case *)
      (false,$1,default_test (),default_summary,default_detail,default_time) }
;
