(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

(* $Id: ctypes.ml,v 1.2 2003-12-15 15:50:56 filliatr Exp $ *)

open Format

module Sset = Set.Make(String)

let stack = ref [ref Sset.empty]

let add s = match !stack with
  | m :: _ -> (*eprintf "add %s@." s;*) m := Sset.add s !m
  | [] -> assert false

let remove s = match !stack with
  | m :: _ -> (*eprintf "remove %s@." s;*) m := Sset.remove s !m
  | [] -> assert false

let mem s = match !stack with
  | m :: _ -> Sset.mem s !m
  | [] -> assert false

let push () = match !stack with
  | (m :: _) as s -> stack := ref !m :: s
  | [] -> assert false

let pop () = match !stack with
  | _ :: s -> stack := s
  | [] -> assert false

      
