(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: cpp.mli,v 1.1 2004-03-02 13:42:28 filliatr Exp $ i*)

(* [cpp f] preprocesses file [f]; returns the preprocessed file and a 
   finalizer to be called when the preprocessed file has been used. *)

val cpp : string -> string * (unit -> unit)
