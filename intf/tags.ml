(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Colors

type loc = { file:string; line:string; sp:string; ep:string }

let last_colored = ref [(GText.tag ())]
let tag = ref 0

let gtktags = Hashtbl.create 57 (* tag id -> gtk tag *)
let loctags = Hashtbl.create 57 (* tag id -> loc *)

let tag_ref = !tag

let new_tag (l:loc) =
  incr tag;
  let mytag = string_of_int !tag in
  Hashtbl.add loctags mytag l;
  mytag

let get_tag t = 
  try 
    Hashtbl.find loctags t
  with Not_found -> 
    assert false

let add_gtktag (index:string) (tag:GText.tag) = 
  Hashtbl.add gtktags index tag

let get_gtktag index = 
  try 
    Hashtbl.find gtktags index
  with Not_found -> 
    assert false

let reset_last_colored () = 
  List.iter 
    (fun tag ->
       tag#set_properties 
	 [`BACKGROUND (get_bc_predicate ()); 
	  `FOREGROUND (get_fc_predicate ())])
    !last_colored;
  last_colored := [GText.tag ()]

let refresh_last_colored tag = 
  reset_last_colored ();
  last_colored := tag

module IntHashtbl = 
  Hashtbl.Make(struct 
                 type t = int 
                 let hash = Hashtbl.hash 
                 let equal = (=) 
               end)
module StringSet = Set.Make(String)
let tag_names = IntHashtbl.create 17
let make_tag (buffer:< tag_table : Gtk.text_tag_table;
              create_tag : ?name:string -> GText.tag_property list -> GText.tag ; .. >)
    ~name l 
    = 
  match GtkText.TagTable.lookup buffer#tag_table name with
  | None -> 
      let oid = Oo.id buffer in
      let old_set = 
        try IntHashtbl.find tag_names oid 
        with Not_found -> StringSet.empty 
      in
      IntHashtbl.replace tag_names oid (StringSet.add name old_set);
      buffer#create_tag ~name l
  | Some t -> new GText.tag t
