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

(*i $Id: creport.ml,v 1.2 2003-12-23 09:18:57 filliatr Exp $ i*)

open Format
open Cerror

exception Error of (Loc.t option) * Cerror.t

let report fmt = function
  | AnyMessage s -> fprintf fmt "Error: %s" s

let raise_located loc e = raise (Error (Some loc, e))
let raise_unlocated e = raise (Error (None, e))
let raise_locop locop e = raise (Error (locop, e))
