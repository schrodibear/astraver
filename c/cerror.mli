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

(*i $Id: cerror.mli,v 1.5 2004-12-02 15:00:25 hubert Exp $ i*)

type t = 
  | AnyMessage of string
  | ExpectedType of Ctypes.ctype * Ctypes.ctype
  | TooManyArguments
  | PartialApp
  | Unsupported of string
	  
