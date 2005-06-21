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

(*i $Id: stat.ml,v 1.1 2005-06-21 14:54:17 filliatr Exp $ i*)

open Format
open Options
open Ast
open Env

let _ = gui := true

let typed_progs = ref []

let deal_file f =
  Loc.set_file f;
  Main.reset ();
  let cin = open_in f in 
  (*c_file := Filename.check_suffix f ".c";*)
  let parsef = (*if !c_file then Main.c_parser else *) Main.ml_parser in
  let p = parsef cin in
  if parse_only then exit 0;
  List.iter Main.interp_decl p;
  typed_progs := (f, List.rev !Main.typed_progs) :: !typed_progs;
  close_in cin

let _ =
  if files = [] then begin eprintf "usage: gwhy files@."; exit 1 end;
  try
    List.iter deal_file Options.files;
    typed_progs := List.rev !typed_progs
  with e ->
    Report.explain_exception err_formatter e;
    pp_print_newline err_formatter ();
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
    
  let create_model () =
    let model = GTree.tree_store cols in
    List.iter toplevel ~f:
      begin fun (month_name, month) ->
	let row = model#append () in
	model#set ~row ~column:name month_name;
	List.iter month ~f:
          begin fun n ->
            let row = model#append ~parent:row () in
            let set column = model#set ~row ~column in
            set name n;
	    set simplify (if Random.bool () then `YES else `STOP);
	    set harvey (if Random.bool () then `YES else `STOP)
          end;
      end;
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
    let _ = view#append_column
      (GTree.view_column ~title:"Simplify" 
	 ~renderer:(icon_renderer, ["stock_id", Model.simplify])
	 ())
    in
    let _ = view#append_column
      (GTree.view_column ~title:"haRVey" 
	 ~renderer:(icon_renderer, ["stock_id", Model.harvey])
	 ())
    in
    ()

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
  View.add_columns ~view ~model;
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
  GMain.Main.main ()
