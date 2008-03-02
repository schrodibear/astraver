(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jc_norm.mli,v 1.16 2008-03-02 20:53:24 nrousset Exp $ *)

open Jc_env
open Jc_fenv
open Jc_ast

val functions_table : 
  (int, fun_info * Loc.position * fun_spec * statement list option) Hashtbl.t

val variables_table : 
  (int, var_info * expr option) Hashtbl.t

val code_function : fun_info * fun_spec * tstatement list option 
  -> var_info list -> fun_info * fun_spec * statement list option

val static_variable : Jc_env.var_info * Jc_ast.texpr option -> var_info * Jc_ast.expr option

(*
val make_int_binary : string -> Loc.position -> expr -> bin_op -> expr -> expr
*)

val one_const : Loc.position -> expr


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
