(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: pretty.mli,v 1.14 2008-11-05 14:03:18 filliatr Exp $ i*)

(* Why pretty-printer *)

val push_decl : ?ergo:bool -> Logic_decl.t -> unit

val reset : unit -> unit

val output_file : string -> unit

(* [output_files f] produces the context in file [f_ctx.why]
   and each goal in a seaparate file [f_po<i>.why] for i=1,2,... *)
val output_files : string -> unit

(* [output_project f] produces a whole project description, in a file
[f.wpr], together with other needed files [f_ctx.why], [f_lemmas.why],
and each goal in a separate file [f_po<i>.why] for i=1,2,... *)
val output_project : string -> Project.t
