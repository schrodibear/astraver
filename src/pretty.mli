(********************************************************************************)
(*                                                                              *)
(*  The Why platform for program certification                                  *)
(*                                                                              *)
(*  Copyright (C) 2002-2010                                                     *)
(*                                                                              *)
(*    Yannick MOY, Univ. Paris-sud 11                                           *)
(*    Jean-Christophe FILLIATRE, CNRS                                           *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                                 *)
(*    Romain BARDOU, Univ. Paris-sud 11                                         *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                        *)
(*                                                                              *)
(*  Secondary contributors:                                                     *)
(*                                                                              *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)                *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)              *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)              *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hypothesis pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                             *)
(*                                                                              *)
(*  This software is free software; you can redistribute it and/or              *)
(*  modify it under the terms of the GNU Lesser General Public                  *)
(*  License version 2.1, with the special exception on linking                  *)
(*  described in file LICENSE.                                                  *)
(*                                                                              *)
(*  This software is distributed in the hope that it will be useful,            *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of              *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                        *)
(*                                                                              *)
(********************************************************************************)



(* Why pretty-printer *)

val push_decl : ?ergo:bool -> Logic_decl.t -> unit

(* [push_or_output_decl d] either pushes the goal in a queue like [push_decl]
   for declarations other than goals, and produces a file for goal 
   declarations much as what [output_files] does. *)
val push_or_output_decl : Logic_decl.t -> unit

val reset : unit -> unit

val output_file : string -> unit

(* [output_files f] produces the context in file [f_ctx.why]
   and each goal in a seaparate file [f_po<i>.why] for i=1,2,... *)
val output_files : string -> unit

(* [output_project f] produces a whole project description, in a file
[f.wpr], together with other needed files [f_ctx.why], [f_lemmas.why],
and each goal in a separate file [f_po<i>.why] for i=1,2,... *)
val output_project : string -> Project.t
