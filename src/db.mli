(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: db.mli,v 1.3 2002-03-11 16:22:38 filliatr Exp $ i*)

open Types
open Ast

(* Here we separate local and global variables, we check the use of
   references and arrays w.r.t the local and global environments, etc. *)

val db_prog : parsed_program -> parsed_program

