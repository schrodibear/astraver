(*
 * The Why and Caduceus certification tools
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

(*i $Id: lib.ml,v 1.3 2004-03-24 08:22:03 filliatr Exp $ i*)


(* small library common to Why and Caduceus *)

let mkdir_p dir =
  if Sys.file_exists dir then begin
    if (Unix.stat dir).Unix.st_kind <> Unix.S_DIR then
      failwith ("failed to create directory " ^ dir)
  end else
    Unix.mkdir dir 0o777

let file ~dir ~file = 
  mkdir_p dir;
  Filename.concat dir (Filename.basename file)

