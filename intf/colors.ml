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

let fcolors = Hashtbl.create 13
let bcolors = Hashtbl.create 13

let _ = 
  Hashtbl.add fcolors "title" "brown";
  Hashtbl.add fcolors "comment" "red";
  Hashtbl.add fcolors "keyword" "darkgreen";
  Hashtbl.add fcolors "var" "darkgreen";
  Hashtbl.add fcolors "predicate" "blue";
  Hashtbl.add fcolors "lpredicate" "blue";
  Hashtbl.add fcolors "information" "orange";
  Hashtbl.add fcolors "separator" "red";
  Hashtbl.add fcolors "hypothesis" "orange";
  Hashtbl.add fcolors "conclusion" "blue";
  Hashtbl.add fcolors "highlight" "black";
  Hashtbl.add fcolors "cc_type" "darkgreen"

let _ = 
  Hashtbl.add bcolors "title" "lightgreen";
  Hashtbl.add bcolors "lpredicate" "lightyellow";
  Hashtbl.add bcolors "highlight" "yellow"

let fc_hilight = "red"
let bc_hilight = "lightgreen"

let get_fc ty = 
  (try Hashtbl.find fcolors ty with Not_found -> "black")

let get_bc ty = 
  (try Hashtbl.find bcolors ty with Not_found -> "white")

let get_color ty = 
  (get_fc ty) , (get_bc ty)

let get_fc_predicate = 
  (try Hashtbl.find fcolors "lpredicate" with Not_found -> "black")

let get_bc_predicate = 
  (try Hashtbl.find bcolors "lpredicate" with Not_found -> "white")

let color_exists ty = 
  (Hashtbl.mem fcolors ty) or (Hashtbl.mem bcolors ty)
