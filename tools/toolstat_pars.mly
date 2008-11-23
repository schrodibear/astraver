/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann R�GIS-GIANAS                                                   */
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

/* $Id: toolstat_pars.mly,v 1.9 2008-11-23 15:16:30 moy Exp $ */

%{
  open Format
  open Parsing
  open Toolstat_types
    
  let default_prover = ""
  let default_test = let count = ref 0 in function () ->
    incr count; "Unknown" ^ (string_of_int !count)
  let default_summary = (0,0,0,0,0)
  let default_detail = ([],[],[],[],[])
  let default_time = (0,0,0.)
  let div_time (h,m,s) n =
    if n = 0 then (h,m,s) else
      let s = float_of_int (3600 * h + 60 * m) +. s in
      let s = s /. float_of_int n in
      let h = int_of_float s / 3600 in
      let m = int_of_float s / 60 - 60 * h in
      let s = s -. float_of_int (3600 * h + 60 * m) in
      (h,m,s)
%}

%token < string > PROJECT
%token < Toolstat_types.prover > PROVER
%token < Toolstat_types.test > TEST
%token < Toolstat_types.result > RESULT
%token < Toolstat_types.time > TIME 

%token EOF
%type < unit > all
%type < Toolstat_types.record list > log
%start log all

%%

all:
| any all { }
| EOF { }
;

any: 
| PROVER { }
| TEST { }
| RESULT { }
| TIME { }
;

log: 
| project_record_list
    { $1 }
| subrecord_list
    { $1 }
| EOF 
    { [] }
;

project_record_list:
| project_record project_record_list 
    { $1 @ $2 }
| project_record
    { $1 }
;

project_record:
| PROJECT subrecord_list
    { List.map (fun (completed,project,prover,test,summary,detail,time) ->
		  let test = $1 ^ ":" ^ test in
		  (completed,Some $1,prover,test,summary,detail,time)
	       ) $2 }
| PROJECT
    { (* Error case *)
      [ (false,Some $1,default_prover,$1,default_summary,default_detail,default_time) ] }
;

subrecord_list:
| subrecord subrecord_list 
    { $1 @ $2 }
| subrecord  
    { $1 }
;

subrecord:
| PROVER tests TIME
    { let n = List.length $2 in
      List.map (fun (test,result) ->
		  let summary,detail = result in
		  (true,None,$1,test,summary,detail,div_time $3 n)
	       ) $2 }
| PROVER TEST RESULT
    { (* Case for no VC *)
      let summary,detail = $3 in [ (true,None,$1,$2,summary,detail,default_time) ] }
| PROVER TEST
    { (* Error case *)
      [ (false,None,$1,$2,default_summary,default_detail,default_time) ] }
| PROVER
    { (* Error case *)
      [ (false,None,$1,default_test (),default_summary,default_detail,default_time) ] }
;

tests:
| TEST RESULT tests
    { ($1,$2) :: $3 }
|   { [] }
;
