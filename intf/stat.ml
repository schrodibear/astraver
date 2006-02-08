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

(*i $Id: stat.ml,v 1.9 2006-02-08 09:08:22 filliatr Exp $ i*)

open Printf
open Options
open Ast
open Env
open Pprinter

let _ = gui := true

let _ =
  try
    Main.main ()
  with e ->
    Report.explain_exception Format.err_formatter e;
    Format.pp_print_newline Format.err_formatter ();
    exit 1

(* GTK *)

(* 
 * let default_screen = Gdk.Screen.default ()
 * let window_width = Gdk.Screen.width ~screen:default_screen ()
 * let window_height = Gdk.Screen.height ~screen:default_screen ()
 *)
let window_width = 1024
let window_height = 700

let monospace_font = ref (Pango.Font.from_string "Monospace 12")
let general_font = ref (Pango.Font.from_string "Monospace 12")

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

let decomp_name =
  let r = Str.regexp "\\(.*\\)_po_\\([0-9]+\\)" in
  fun s ->
    if Str.string_match r s 0 then
      Str.matched_group 1 s, Str.matched_group 2 s
    else
      s, "1"

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
  let fullname = cols#add string
  let simplify = cols#add GtkStock.conv
  let harvey = cols#add GtkStock.conv
  let cvcl = cols#add GtkStock.conv

  (* all obligations *)
  let obligs = Hashtbl.create 97
  let find_oblig = Hashtbl.find obligs

  (* obligation name -> its model row *)
  let orows = Hashtbl.create 97 
  
  (* function -> its model row *)
  let frows = Hashtbl.create 17 
  let find_fct = Hashtbl.find frows

  (* functions *)
  let fq = Queue.create ()
    
  let create_model () =
    let model = GTree.tree_store cols in
    Dispatcher.iter
      (fun ((_,s,_) as o) ->
	 Hashtbl.add obligs s o;
	 let f,n = decomp_name s in
	 let row =
	   try 
	     Hashtbl.find frows f
	   with Not_found ->
	     let row = model#append () in
	     Queue.add f fq;
	     Hashtbl.add frows f row;
	     model#set ~row ~column:name f;
	     model#set ~row ~column:fullname f;
	     row
	 in
	 let row_n = model#append ~parent:row () in
	 Hashtbl.add orows s row_n;
	 model#set ~row:row_n ~column:name n;
	 model#set ~row:row_n ~column:fullname s;
	 model#set ~row:row_n ~column:simplify `REMOVE;
	 model#set ~row:row_n ~column:harvey `REMOVE;
	 model#set ~row:row_n ~column:cvcl `REMOVE;
      );
    model
      
end

module View = struct

  open GtkTree
    
  let add_columns ~(view : GTree.view) ~model =
    let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
    let icon_renderer = GTree.cell_renderer_pixbuf [ `STOCK_SIZE `BUTTON ] in
    let _ = view#append_column
      (GTree.view_column ~title:"Proof obligations " 
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

    let vc_cvcl = 
      GTree.view_column ~title:"CVC Lite" 
	~renderer:(icon_renderer, ["stock_id", Model.cvcl]) ()
    in
    vc_cvcl#set_clickable true;
    let _ = view#append_column vc_cvcl in

    vc_simplify, vc_harvey, vc_cvcl

end

(* 
 * Timeout 
 *)
let timeout = ref 10
let set_timeout v = timeout := v

(*
 * Default prover
 *)
let default_prover = ref Dispatcher.Simplify
let set_prover p = default_prover := p
let print_prover p = match p with 
  | Dispatcher.Simplify -> "Simplify"
  | Dispatcher.Harvey -> "Harvey"
  | Dispatcher.Cvcl -> "Cvc Lite"
let get_prover = function
  | Dispatcher.Simplify -> Model.simplify 
  | Dispatcher.Harvey -> Model.harvey
  | Dispatcher.Cvcl -> Model.cvcl

let prove fct = 
  ignore (Thread.create fct ())

(* 
 * Returns children of a function 
 *)
let children f n = 
  let q = Queue.create () in
  for i = 1 to n do
    let child = Hashtbl.find Model.obligs (f^"_po_"^(string_of_int i)) in
    Queue.add child q
  done;
  q

(* 
 * run a prover on an obligation and update the model 
 *)
let run_prover_child p column_p (view:GTree.view) (model:GTree.tree_store) o = 
  let (_, oblig, _) = o in
  try 
    let row = Hashtbl.find Model.orows oblig in
    model#set ~row ~column:column_p `EXECUTE;
    let r = Dispatcher.call_prover ~obligation:oblig ~timeout:!timeout p 
    and s = ref 0 in
    model#set ~row ~column:column_p
      (match r with 
	 | Calldp.Valid -> s:=1; `YES 
	 | Calldp.ProverFailure _ -> `NO
	 | Calldp.Timeout -> `CUT
	 | _ -> `STOP);
    !s
  with Not_found -> begin
    print_endline ("     [...] Error : obligation \""^oblig^"\" not found !"); 
    flush stdout;
    0
  end

let run_prover_oblig p column_p (view:GTree.view) (model:GTree.tree_store) s () = 
  try 
    let oblig = Hashtbl.find Model.obligs s in
    let _ = run_prover_child p column_p view model oblig in
    ()
  with Not_found -> begin
    print_endline ("     [...] Error : obligation \""^s^"\" not found !"); 
    flush stdout;
  end

(*
 * run a prover on a function and update the model 
 *)
let run_prover_fct p column_p (view:GTree.view) (model:GTree.tree_store) f () = 
  try
    let row = Model.find_fct f in
    let n = model#iter_n_children (Some(row)) in
    let mychildren = children f n in
    let succeed = Queue.fold
      (fun nb oblig -> 
	 let result = run_prover_child p column_p view model oblig in
	 result + nb)
      0
      mychildren in
    if succeed = n then 
      begin 
	model#set ~row ~column:column_p `APPLY;
	let path = model#get_path row in
	view#collapse_row path
      end
    else 
      begin 
	model#set ~row ~column:column_p `CANCEL;
	let path = model#get_path row in
	view#expand_row path
      end;
    let statistics = (string_of_int (succeed * 100 / n)) in
    !flash_info ("Function \""^f^"\" statistics : "^statistics^" %");
    model#set ~row ~column:Model.name (f^" [ "^(print_prover p)^" -> "^statistics^" %]")
  with Not_found -> 
    begin 
      print_endline ("     [...] Error : function \""^f^"\" not found !"); 
      flush stdout 
    end

(*
 * run a prover on all obligations and update the model 
 *)
let run_prover_all p column_p (view:GTree.view) (model:GTree.tree_store) () =
  Queue.iter 
    (fun f -> run_prover_fct p column_p view model f ()) 
    Model.fq

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
  let refresh_m = file_factory#add_image_item ~stock:`REFRESH ~label:"Refresh"
    ~key:GdkKeysyms._R () in
  let _ = file_factory#add_separator () in
  let quit_m = file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"Quit" 
    ~callback:(fun () -> exit 0) () in

  (* configuration menu *)
  let configuration_menu = factory#add_submenu "Configuration" in
  let configuration_factory = new GMenu.factory configuration_menu ~accel_group in
  let customize_colors_m =
    configuration_factory#add_image_item ~label:"Customize colors" 
      ~stock:`SELECT_COLOR
      ~callback:(fun () -> !flash_info "Not implemented") () in
  let customize_fonts_m = 
    configuration_factory#add_image_item ~label:"Customize fonts" 
      ~stock:`SELECT_FONT
      ~callback:(fun () -> !flash_info "Not implemented") () in
  let _ = configuration_factory#add_separator ()  in
  (* menus for povers *)
  let simplify_m = configuration_factory#add_check_item ~active:true
    ~callback:(fun b -> default_prover := Dispatcher.Simplify) "Simplify" in
  let provers = Some(simplify_m#as_item) in
  let harvey_m = configuration_factory#add_check_item ~active:false
    ~callback:(fun b -> default_prover := Dispatcher.Harvey) "Harvey" in
  let cvcl_m = configuration_factory#add_check_item ~active:false 
    ~callback:(fun b -> default_prover := Dispatcher.Cvcl) "CVC Lite" in
  let simplify_callback () = 
    simplify_m#set_active true;
    harvey_m#set_active false;
    cvcl_m#set_active false;
    set_prover Dispatcher.Simplify;
    !flash_info "Simplify selected for default mode" in
  let harvey_callback () =
    simplify_m#set_active false;
    harvey_m#set_active true;
    cvcl_m#set_active false;
    set_prover Dispatcher.Harvey; 
    !flash_info "Harvey selected for default mode" in
  let cvcl_callback () = 
    simplify_m#set_active false;
    harvey_m#set_active false;
    cvcl_m#set_active true;
    set_prover Dispatcher.Cvcl; 
    !flash_info "Cvc Lite selected for default mode" in
  let _ = simplify_m#event#connect#button_release 
    ~callback:(fun ev -> simplify_callback (); true) in
  let _ = harvey_m#event#connect#button_release 
    ~callback:(fun ev -> harvey_callback (); true) in
  let _ = cvcl_m#event#connect#button_release 
    ~callback:(fun ev -> cvcl_callback (); true) in

  let switch_next_prover () = 
    match !default_prover with
      | Dispatcher.Simplify -> harvey_callback ()
      | Dispatcher.Harvey -> cvcl_callback ()
      | Dispatcher.Cvcl -> simplify_callback ()
  in 
  let _ = configuration_factory#add_separator ()  in
  let next_prover_m = configuration_factory#add_image_item ~key:GdkKeysyms._N 
    ~label:"Switch to next prover" ~callback:switch_next_prover () in
  
  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in

  (* left tree of proof obligations *)
  let model = Model.create_model () in
  let scrollview = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:250 ~packing:hp#add1 () in
  let view = GTree.view ~model ~packing:scrollview#add_with_viewport () in
  let _ = view#selection#set_mode `SINGLE in
  let _ = view#set_rules_hint true in
  let vc_simplify,vc_harvey,vc_cvcl = View.add_columns ~view ~model in
  let expand_all_m = configuration_factory#add_image_item ~key:GdkKeysyms._E 
    ~label:"Expand all" ~callback:(fun () -> view#expand_all ()) () in
  let collapse_all_m = configuration_factory#add_image_item ~key:GdkKeysyms._C 
    ~label:"Collapse all" ~callback:(fun () -> view#collapse_all ()) () in

  (* proof menu *)
  let proof_menu = factory#add_submenu "Proof" in
  let proof_factory = new GMenu.factory proof_menu ~accel_group in 
  let all_m = proof_factory#add_image_item ~label:"Prove all obligations" 
    ~key:GdkKeysyms._A 
    ~callback:(fun () -> prove (run_prover_all !default_prover (get_prover !default_prover) view model)) () in
  let fct_callback () = 
    List.iter 
      (fun p -> 
	 let row = model#get_iter p in
	 let s = model#get ~row ~column:Model.fullname in 
	 if model#iter_has_child row then
	   prove (run_prover_fct !default_prover (get_prover !default_prover) view model s)
	 else let name,_ = decomp_name s in 
	 prove (run_prover_fct !default_prover (get_prover !default_prover) view model name))
      view#selection#get_selected_rows in
  let fct_m = proof_factory#add_image_item ~label:"Prove selected function" 
    ~key:GdkKeysyms._F ~callback:fct_callback () in
  let oblig_callback () =
    List.iter 
      (fun p -> 
	 let row = model#get_iter p in
	 let s = model#get ~row ~column:Model.fullname in 
	 if model#iter_has_child row then
	   let name = s^"_po_1" in
	   prove (run_prover_oblig !default_prover (get_prover !default_prover) view model name)
	 else 
	   prove (run_prover_oblig !default_prover (get_prover !default_prover) view model s))
      view#selection#get_selected_rows in
  let oblig_m = proof_factory#add_image_item ~label:"Prove selected obligation" 
    ~key:GdkKeysyms._O ~callback:oblig_callback () in


  (* run Simplify on all proof obligations *)
  (* ???? why can't I make a function for this callback? *)
  let _ = vc_simplify#connect#clicked 
    (fun () -> 
       prove (run_prover_all Dispatcher.Simplify Model.simplify view model)) 
  in
  
  (* run Harvey on all proof obligations *)
  let _ = vc_harvey#connect#clicked
    (fun () -> 
       prove (run_prover_all Dispatcher.Harvey Model.harvey view model))
  in
  (* run CVC Lite on all proof obligations *)
  let _ = vc_cvcl#connect#clicked
    (fun () -> 
       prove (run_prover_all Dispatcher.Cvcl Model.cvcl view model))
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

  (* bottom line *)
  let hbox = GPack.hbox ~packing:vbox#pack () in

  (* status bar *)
  let status_bar = 
    GMisc.statusbar ~packing:(hbox#pack ~fill:true ~expand:true) () 
  in
  status_bar#misc#modify_font !statusbar_font ;
  let status_context = status_bar#new_context "messages" in
  ignore (status_context#push "Welcome to the Why GUI");
  display_info := (fun s -> 
		     status_context#pop ();
		     ignore (status_context#push s));
  flash_info := (fun s -> status_context#flash ~delay:2000 s);
 
  (* timeout set *)
  let _ = GMisc.label ~text:"Timeout" ~xalign:0. ~packing:hbox#pack () in
  let timeout = GEdit.spin_button ~digits:0 ~packing:hbox#pack () in
  timeout#adjustment#set_bounds ~lower:1. ~upper:999. ~step_incr:1. ();
  timeout#adjustment#set_value 10.;
  let _ = 
    timeout#connect#value_changed ~callback:
      (fun () -> set_timeout timeout#value_as_int)
  in

  (* lower text view: source code *)
  let tv2 = GText.view ~packing:(sw2#add) () in
  let _ = tv2#misc#modify_font !lower_view_general_font in
  let _ = tv2#set_editable false in
  let _ = tv2#set_wrap_mode `WORD in
  let tb2 = tv2#buffer in

  (* upper text view: obligation *)
  let buf1 = GText.buffer () in 
  let tv1 = GText.view ~buffer:buf1 ~packing:(sw1#add) () in
  let _ = tv1#misc#modify_font !upper_view_general_font in
  let _ = tv1#set_editable false in
  let _ = tv1#set_wrap_mode `WORD in
  let _ = GtkBase.Widget.add_events tv1#as_widget
    [`ENTER_NOTIFY; `LEAVE_NOTIFY; `POINTER_MOTION] in
  let _ = tv1#event#connect#motion_notify
    ~callback:
    (fun e -> 
       let win = match tv1#get_window `WIDGET with
	 | None -> assert false
	 | Some w -> w
       in
       let x,y = Gdk.Window.get_pointer_location win in
       let b_x,b_y = tv1#window_to_buffer_coords 
	 ~tag:`WIDGET 
	 ~x 
	 ~y 
       in
       let it = tv1#get_iter_at_location ~x:b_x ~y:b_y in
       let tags = it#tags in
       List.iter 
	 ( fun t ->
	     ignore (GtkText.Tag.event 
		       t#as_tag
		       tv2#as_widget
		       e 
		       it#as_iter))
	 tags;
       if tags = [] then Pprinter.reset_last_colored ();
       false)
  in

  let update_buffer tv =
    let buf = GText.buffer () in
    tv#set_buffer buf;
    buf
  in
  
  (*
   * obligation selection 
   *)
  let _ =
    view#selection#connect#after#changed ~callback:
      begin fun () ->
        List.iter
          (fun p ->
             let row = model#get_iter p in
             let s = model#get ~row ~column:Model.fullname in
             try
               let o = Model.find_oblig s in
               let buf = update_buffer tv1 in
               buf#set_text "";
               Pprinter.text_of_obligation tv1 tv2 o
             with Not_found -> ())
          view#selection#get_selected_rows;
      end
  in

  (*
   * Running obligation 
   *)
  ignore (view#event#connect#button_press ~callback:
	    (fun ev -> 
	       if GdkEvent.Button.button ev = 3 then 
		 List.iter 
		   (fun p -> 
		      let row = model#get_iter p in
		      let s = model#get ~row ~column:Model.fullname in
		      let column = get_prover !default_prover in
		      if model#iter_has_child row then
			prove (run_prover_fct !default_prover column view model s)
		      else 
			prove (run_prover_oblig !default_prover column view model s)
		   )
		   view#selection#get_selected_rows;
	       false
	    ));

  (*
   * Remove default pango menu for textviews 
   *)
  ignore (tv1#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));
  ignore (tv2#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));

  (*
   * Startup configuration 
   *)
  buf1#place_cursor ~where:buf1#start_iter;

  w#add_accel_group accel_group;
  w#show ()

let _ = 
  ignore (GtkMain.Main.init ());
  main () ;
  GtkThread.main ()
