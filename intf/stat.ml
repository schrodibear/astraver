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

(*i $Id: stat.ml,v 1.4 2005-06-22 15:07:43 filliatr Exp $ i*)

open Printf
open Options
open Ast
open Env

let _ = gui := true

let _ =
  try
    Main.main ()
  with e ->
    Report.explain_exception Format.err_formatter e;
    Format.pp_print_newline Format.err_formatter ();
    exit 1

(* GTK *)

let window_width = 800
let window_height = 900

let monospace_font = ref (Pango.Font.from_string "Monospace 15")
let general_font = ref (Pango.Font.from_string "Monospace 15")

let lower_view_general_font = general_font
let upper_view_general_font = general_font
let statusbar_font = ref !general_font
let proved_lemma_font = ref !monospace_font
let to_prove_lemma_font = ref !monospace_font
let discharged_lemma_font = ref !monospace_font
let display_info = ref (function s -> failwith "not ready")
let flash_info = ref (function s -> failwith "not ready")

let out_some = function None -> assert false | Some f -> f

let try_convert s = 
  try
    if Glib.Utf8.validate s then s else 
      Glib.Convert.locale_to_utf8 s
  with _ -> failwith ("Fatal error: wrong encoding in string \""^s^"\"")

let path_of_int i = 
  GtkTree.TreePath.from_string (string_of_int (if i < 0 then 0 else i))

let to_refresh reference e = 
  let n = Filename.chop_extension reference ^ e in
  not (Sys.file_exists n) ||
  ((Unix.stat reference).Unix.st_mtime > (Unix.stat n).Unix.st_mtime)

module Model = struct

  open StdLabels

  let f =
    [ "1"; "2"; "3" ]

  let g =
    [ "1"; "2" ]

  let toplevel =
    [ "f", f;
      "g", g;
    ]
      
  open Gobject.Data
      
  let cols = new GTree.column_list
  let name = cols#add string
  let simplify = cols#add GtkStock.conv
  let harvey = cols#add GtkStock.conv

  let decomp_name =
    let r = Str.regexp "\\(.*\\)_po_\\([0-9]+\\)" in
    fun s ->
      if Str.string_match r s 0 then
	Str.matched_group 1 s, Str.matched_group 2 s
      else
	s, "1"

  (* obligation -> its model row *)
  let orows = Hashtbl.create 97
    
  let create_model () =
    let model = GTree.tree_store cols in
    let rows = Hashtbl.create 17 in
    Dispatcher.iter
      (fun (_,s,_) ->
	 let f,n = decomp_name s in
	 let row =
	   try 
	     Hashtbl.find rows f
	   with Not_found ->
	     let row = model#append () in
	     Hashtbl.add rows f row;
	     model#set ~row ~column:name f;
	     row
	 in
	 let row_n = model#append ~parent:row () in
	 Hashtbl.add orows s row_n;
	 model#set ~row:row_n ~column:name n;
	 model#set ~row:row_n ~column:simplify `EXECUTE;
	 model#set ~row:row_n ~column:harvey `EXECUTE;
      );
    model
      
end

module View = struct

  open GtkTree
    
  let add_columns ~(view : GTree.view) ~model =
    let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
    let icon_renderer = GTree.cell_renderer_pixbuf [ `STOCK_SIZE `BUTTON ] in
    let _ = view#append_column
      (GTree.view_column ~title:"Proof obligation" 
	 ~renderer:(renderer, ["text", Model.name])
	 ())
    in
    let vc_simplify = 
      GTree.view_column ~title:"Simplify" 
	~renderer:(icon_renderer, ["stock_id", Model.simplify]) ()
    in
    vc_simplify#set_clickable true;
    let _ = view#append_column vc_simplify in
    let vc_harvey = 
      GTree.view_column ~title:"haRVey" 
	~renderer:(icon_renderer, ["stock_id", Model.harvey]) ()
    in
    vc_harvey#set_clickable true;
    let _ = view#append_column vc_harvey in
    vc_simplify, vc_harvey

end


let main () = 
  let w = GWindow.window 
	    ~allow_grow:true ~allow_shrink:true
	    ~width:window_width ~height:window_height ~title:"Why viewer" ()
  in
  w#misc#modify_font !general_font;
  let accel_group = GtkData.AccelGroup.create () in
  let _ = w#connect#destroy ~callback:(fun () -> exit 0) in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  (* Menu *)
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in
  let factory = new GMenu.factory menubar in
  let accel_group = factory#accel_group in
  let file_menu = factory#add_submenu "File" in
  let file_factory = new GMenu.factory file_menu ~accel_group in
  let quit_m = file_factory#add_item "Quit" ~key:GdkKeysyms._Q
	       ~callback:(fun () -> exit 0) in
  let refresh_m = file_factory#add_item "Refresh" ~key:GdkKeysyms._R in
  let configuration_menu = factory#add_submenu "Configuration" in
  let configuration_factory = new GMenu.factory configuration_menu ~accel_group
  in
  let customize_colors_m =
    configuration_factory#add_item "Customize colors"
    ~callback:(fun () -> !flash_info "Not implemented")
  in
  let customize_fonts_m = 
    configuration_factory#add_item "Customize fonts"
    ~callback:(fun () -> !flash_info "Not implemented")
  in

  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in

  (* left tree of proof obligations *)
  let model = Model.create_model () in
  let view = GTree.view ~model ~packing:hp#add1 () in
  let _ = view#selection#set_mode `SINGLE in
  let _ = view#set_rules_hint true in
  let vc_simplify,vc_harvey = View.add_columns ~view ~model in

  (* run a prover on all obligations and update the model *)
  let run_prover p column_p () =
    Dispatcher.iter
      (fun (_,s,_) ->
	 let row = Hashtbl.find Model.orows s in
	 let r = Dispatcher.call_prover s p in
	 model#set ~row ~column:column_p
	   (match r with Calldp.Valid -> `YES | _ -> `STOP))
  in

  (* run Simplify on all proof obligations *)
  (* ???? why can't I make a function for this callback? *)
  let _ = vc_simplify#connect#clicked 
    (fun () -> 
       ignore 
	 (Thread.create (run_prover Dispatcher.Simplify Model.simplify) ()))
  in
  (* run Harvey on all proof obligations *)
  let _ = vc_harvey#connect#clicked
    (fun () -> 
       ignore 
	 (Thread.create (run_prover Dispatcher.Harvey Model.harvey) ()))
  in

  let _ = view#misc#connect#realize ~callback:view#expand_all in

  (* vertical paned *)
  let hb = GPack.paned `VERTICAL  ~border_width:3 ~packing:hp#add2 () in
  let _ = hb#misc#connect#realize
	  ~callback:(fun _ ->hb#set_position (window_height*6/10 ) ) in
  let _ = hb#set_position (window_height*9/10 ) in

  (* upper frame *)
  let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add1 () in 
  let sw1 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr1#add () 
  in

  (* lower frame *)
  let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add2 () in 
  let sw2 = GBin.scrolled_window 
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:(fr2#add) () 
  in

  (* status bar (at bottom) *)
  let status_bar = GMisc.statusbar ~packing:vbox#pack () in
  status_bar#misc#modify_font !statusbar_font ;
  let status_context = status_bar#new_context "messages" in
  ignore (status_context#push "Ready");
  ignore (status_context#push "Ready");
  display_info := (fun s -> 
		     status_context#pop ();
		     ignore (status_context#push s));
  flash_info := !display_info (* fun s -> status_context#flash ~delay:10 s *);

  (* lower text view: annotations *)
  let tv2 = GText.view ~packing:(sw2#add) () in
  let _ = tv2#misc#modify_font !lower_view_general_font in
  let _ = tv2#set_editable false in
  let tb2 = tv2#buffer in

  (* upper text view: source code *)
  let buf1 = GText.buffer () in 
  let tv1 = GText.view ~buffer:buf1 ~packing:(sw1#add) () in
  let _ = tv1#misc#modify_font !upper_view_general_font in
  let _ = tv1#set_editable false in

  (* Remove default pango menu for textviews *)
  ignore (tv1#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));
  ignore (tv2#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));

  (* startup configuration *)
  buf1#place_cursor ~where:buf1#start_iter;

  w#add_accel_group accel_group;

  w#show ()

let _ = 
  ignore (GtkMain.Main.init ());
  main () ;
  GtkThread.main ()
  (*GMain.Main.main ()*)
