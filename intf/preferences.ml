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

open Tools
open Colors

let set_window_settings w = 
  let _ = w#event#connect#key_press ~callback:
    (fun k -> if GdkEvent.Key.keyval k = GdkKeysyms._Escape then w#destroy ();false)
  in
  w#set_modal true;
  w#set_skip_pager_hint true;
  w#set_skip_pager_hint true

let save_settings () = ()
	
let preferences () =
  let w = GWindow.window 
    ~allow_grow:false ~allow_shrink:true
    ~border_width:20
    ~title:"Preferences" () in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in
  let table = GPack.table ~homogeneous:true ~packing:vbox#add () in
  
  (* elements *)
  let live_l = GMisc.label ~text:"Live update" () in
  let live = GButton.check_button 
    ~label:"Enable live update mode" 
    ~active:(Tools.live_update ()) ~packing:vbox#add () in
  let cache_l = GMisc.label ~text:"Cache" () in
  let cache = GButton.check_button 
    ~label:"Enable cache" 
    ~active:(Cache.is_enabled ()) ~packing:vbox#add () in
  let hardproof = GButton.check_button 
    ~label:"Hard proof mode" 
    ~active:(Cache.try_proof ()) ~packing:vbox#add () in

  let misc_l = GMisc.label ~text:"Misc" () in
  let timeout_l = GMisc.label ~text:"Timeout" ~justify:`LEFT () in
  let timeout = GEdit.spin_button ~digits:0 () in
  timeout#adjustment#set_bounds ~lower:1. ~upper:999. ~step_incr:1. ();
  timeout#adjustment#set_value 10.;

  let pr_names = List.map (fun p -> p.Model.pr_name) Model.provers in
  let provers_l = GMisc.label ~text:"Default prover" ~justify:`LEFT () in
  let provers = GEdit.combo ~popdown_strings:pr_names ~allow_empty:false ~value_in_list:true () in
  let quit () = 
    save_settings ();
    w#destroy () 
  in
  let hbox = GPack.hbox ~homogeneous:true ~packing:vbox#add () in
  let button_ok = GButton.button ~label:"OK" ~stock:`OK ~packing:hbox#add () in
  let _ = button_ok#connect#clicked ~callback:quit in
  let button_cancel = GButton.button ~label:"Cancel" ~stock:`CANCEL ~packing:hbox#add () in
  let _ = button_cancel#connect#clicked ~callback:(w#destroy) in
  
  (* placing elements *)
  table#attach ~left:0 ~top:0 ~right:2 (misc_l#coerce);
  table#attach ~left:0 ~top:1 (timeout_l#coerce);
  table#attach ~left:1 ~top:1 (timeout#coerce);
  table#attach ~left:0 ~top:2 (provers_l#coerce);
  table#attach ~left:1 ~top:2 (provers#coerce);
  table#attach ~left:0 ~top:4 ~right:2 (cache_l#coerce);
  
  (* window settings *)
  set_window_settings w;
  w#show ()

let color () =
  let w = GWindow.window 
    ~allow_grow:false ~allow_shrink:true
    ~border_width:20
    ~title:"Colors" () in
  let quit result () = 
    List.iter
      (fun (k, tf, tb) -> Colors.replace_color k (tf#text) (tb#text))
      result;
    save_settings ();
    w#destroy ()
  in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in
  let table = GPack.table ~homogeneous:true ~packing:vbox#add () in
  (* colors *)
  let colors_l = GMisc.label ~text:"Colors (forecolor, backcolor)" () in
  table#attach ~left:0 ~top:0 ~right:3 (colors_l#coerce);
  let r = ref 2 in
  let result = 
    List.map
      (fun {key=k; name=n; fc=f; bc=b} -> 
	 let l = GMisc.label ~text:n () in
	 let tf = GEdit.entry ~text:f () in
	 let tb = GEdit.entry ~text:b () in
	 table#attach ~left:0 ~top:!r (l#coerce);
	 table#attach ~left:1 ~top:!r (tf#coerce);
	 table#attach ~left:2 ~top:!r (tb#coerce);
	 incr r;
	 (k, tf, tb))
      (Colors.get_all_colors ()) in
  
  let hbox = GPack.hbox ~homogeneous:true ~packing:vbox#add () in
  let button_ok = GButton.button ~label:"OK" ~stock:`OK ~packing:hbox#add () in
  let _ = button_ok#connect#clicked ~callback:(quit result) in
  let button_cancel = GButton.button ~label:"Cancel" ~stock:`CANCEL ~packing:hbox#add () in
  let _ = button_cancel#connect#clicked ~callback:(w#destroy) in
  
  (* window settings *)
  set_window_settings w;
  w#show ()
  

(* Main *)
let show window_type () = 
  ignore (GtkMain.Main.init ());
  (match window_type with
     | Preferences -> preferences ()
     | Color -> color ()
     | _ -> ());
  GtkThread.main ()
