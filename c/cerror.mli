(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: cerror.mli,v 1.4 2004-03-24 07:40:37 filliatr Exp $ i*)

type t = 
  | AnyMessage of string
  | ExpectedType of Cast.tctype * Cast.tctype
  | TooManyArguments
  | PartialApp
  | Unsupported of string
	  
