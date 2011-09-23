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

open Tags

type window = 
  | Color
  | About
  | Help

let grab_infos = 
  let r_loc = Str.regexp "File \"\\(.+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)" in
  fun s -> 
    if Str.string_match r_loc s 0 then 
      let source = Filename.concat (Sys.getcwd ()) (Str.matched_group 1 s) in
      Some({file=source;
            line=(Str.matched_group 2 s);
            sp=(Str.matched_group 3 s);
            ep=(Str.matched_group 4 s)})
    else None

let decomp_name =
  let r = Str.regexp "\\(.*\\)_po_\\([0-9]+\\)" in
  fun s ->
    if Str.string_match r s 0 then
      Str.matched_group 1 s, Str.matched_group 2 s
    else
      "", s

(*
 * Live update
 *)
let live = ref true
let swap_live () = live := not !live
let set_live v = live := v
let live_update () = !live

(* 
 * Timeout 
 *)
let timeout = ref 10
let set_timeout v = timeout := v
let get_timeout () = !timeout


(* 

images, icons

*)

(* todo: size should adapt to current font_size ! *)
let image ?size f =
  let name =
    if !Colors.colorblind then f^"-bw.png" else f^"32.png" 
  in
  let n = Filename.concat Options.lib_dir (Filename.concat "images" name)
  in
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n

let boomy = ref false

let set_boomy b = boomy := b

let is_boomy () = !boomy 


let iconname_default = "pause"
let iconname_running = "play"
let iconname_valid = "accept"
let iconname_unknown = "help"
let iconname_invalid = "delete"
let iconname_timeout = "clock"
let iconname_failure = "bug"
let iconname_yes = "accept"
let iconname_no = "delete"
let iconname_down = "play"

let image_default = ref (image ~size:32 iconname_default)
let image_running = ref !image_default
let image_valid = ref !image_default
let image_unknown = ref !image_default
let image_invalid = ref !image_default
let image_timeout = ref !image_default
let image_failure = ref !image_default
let image_yes = ref !image_default
let image_no = ref !image_default
let image_down = ref !image_default

let resize_images size =
  image_default := image ~size iconname_default;
  image_running := image ~size iconname_running;
  image_valid := image ~size iconname_valid;
  image_unknown := image ~size iconname_unknown;
  image_invalid := image ~size iconname_invalid;
  image_timeout := image ~size iconname_timeout;
  image_failure := image ~size iconname_failure;
  image_yes := image ~size iconname_yes;
  image_no := image ~size iconname_no;
  image_down := image ~size iconname_down


let () = resize_images (!Colors.font_size * 2 - 4)
  
  
