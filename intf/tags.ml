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

open Colors

type loc = { file:string; line:string; sp:string; ep:string }

let last_colored = ref (GText.tag ())

let gtktags = Hashtbl.create 57
let loctags = Hashtbl.create 57

let new_tag = 
  let tag = ref 0 in
  fun (l:loc) ->
    incr tag;
    let mytag = string_of_int !tag in
    Hashtbl.add loctags mytag l;
    mytag

let get_tag t = 
  try 
    Hashtbl.find loctags t
  with Not_found -> assert false

let add_gtktag (index:string) (tag:GText.tag) = 
  Hashtbl.add gtktags index tag

let get_gtktag index = 
  try 
    Hashtbl.find gtktags index
  with Not_found -> assert false


let reset_last_colored () = 
  !last_colored#set_properties 
    [`BACKGROUND get_bc_predicate; `FOREGROUND get_fc_predicate];
  last_colored := GText.tag ()

let refresh_last_colored tag = 
  reset_last_colored ();
  last_colored := tag
