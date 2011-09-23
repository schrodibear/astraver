(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



module Sset : Set.S with type elt = string

val mkdir_p : string -> unit

(* [file dir file] returns "dir/basename" if [file] is "dirname/basename", 
   creating [dir] if necessary. *)
val file : dir:string -> file:string -> string

(* [file_subdir dir file] returns "dirname/dir/basename" if [file] is "dirname/basename", 
   creating [dir] if necessary. *)
val file_subdir : dir:string -> file:string -> string

(* [file_copy f1 f2] copies [f1] into name [f2] *)
val file_copy : string -> string -> unit

(* [file_copy_if_different f1 f2] copies [f1] into name [f2], unless
   [f2] already exists and is identical to [f1] (thus keeping the same
   modification date) *)
val file_copy_if_different : string -> string -> unit

(* return the content of an in-channel *)
val channel_contents : in_channel -> string

(* return the content of a file *)
val file_contents : string -> string

(* return the content of a file *)
val file_contents_buf : string -> Buffer.t

(* remove file if debug not set, or display appropriate info message *)
val remove_file : debug:bool -> string -> unit
