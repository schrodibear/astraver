
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: db.mli,v 1.1 2001-08-17 00:52:37 filliatr Exp $ *)

open Types
open Ast

(* Here we separate local and global variables, we check the use of
   references and arrays w.r.t the local and global environments, etc. *)

val db_type_v : Ident.t list -> type_v -> type_v

val db_prog : parsed_program -> parsed_program

