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

(*i $Id: stat.ml,v 1.20 2006-03-15 13:23:54 dogguy Exp $ i*)

open Printf
open Options
open Ast
open Env
open Cache
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
      "goals", s

module Model = struct

  type prover = {
    pr_name : string;
    pr_result : string GTree.column;
    pr_icon : GtkStock.id GTree.column;
    pr_id : Dispatcher.prover;
  }

  open Gobject.Data
      
  let cols = new GTree.column_list
  let name = cols#add string
  let fullname = cols#add string
  let total = cols#add int
  let result = cols#add int

  let simplify = {
    pr_name = "Simplify";
    pr_result = cols#add string;
    pr_icon = cols#add GtkStock.conv;
    pr_id = Dispatcher.Simplify;
  }
  let zenon = {
    pr_name = "Zenon";
    pr_result = cols#add string;
    pr_icon = cols#add GtkStock.conv;
    pr_id = Dispatcher.Zenon;
  }
  let harvey = {
    pr_name = "haRVey";
    pr_result = cols#add string;
    pr_icon = cols#add GtkStock.conv;
    pr_id = Dispatcher.Harvey;
  }
  let cvcl = {
    pr_name = "CVCL";
    pr_result = cols#add string;
    pr_icon = cols#add GtkStock.conv;
    pr_id = Dispatcher.Cvcl;
  }

  let provers = [simplify; zenon; harvey; cvcl]
  let () = assert (List.length provers > 0)

  (* all obligations *)
  let obligs = Hashtbl.create 97
  let find_oblig = Hashtbl.find obligs

  (* obligation name -> its model row *)
  let orows = Hashtbl.create 97 
  
  (* function -> its model row *)
  let frows = Hashtbl.create 17 
  let find_fct = Hashtbl.find frows

  (* function -> list of its obligations *)
  let fobligs = Hashtbl.create 97
  let find_fobligs = Hashtbl.find fobligs
  let iter_fobligs fct f = Queue.iter f (Hashtbl.find fobligs fct)

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
	     Hashtbl.add fobligs f (Queue.create ());
	     model#set ~row ~column:name f;
	     model#set ~row ~column:fullname f;
	     model#set ~row ~column:total 0;
	     List.iter 
	       (fun p -> model#set ~row ~column:p.pr_result "0") 
	       provers;
	     row
	 in
	 let row_n = model#append ~parent:row () in
	 Hashtbl.add orows s row_n;
	 Queue.add row_n (Hashtbl.find fobligs f);
	 model#set ~row:row_n ~column:name n;
	 model#set ~row:row_n ~column:fullname s;
	 model#set ~row:row_n ~column:result 0;
	 List.iter
	   (fun p -> model#set ~row:row_n ~column:p.pr_icon `REMOVE)
	   provers
      );
    model
      
end

module View = struct

  open GtkTree
  open Model

  let add_columns ~(view : GTree.view) ~model =
    let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
    let icon_renderer = GTree.cell_renderer_pixbuf [ `STOCK_SIZE `BUTTON ] in
    let _ = view#append_column
      (GTree.view_column ~title:"Proof obligations " 
	 ~renderer:(renderer, ["text", Model.name])
	 ())
    in
    List.map
      (fun p ->
	 let vc = 
	   GTree.view_column ~title:p.pr_name 
	     ~renderer:(icon_renderer, ["stock_id", p.pr_icon]) ()
	 in
	 vc#set_clickable true;
	 let _ = view#append_column vc in
	 p, vc)
      provers

end

let update_buffer tv =
  let buf = GText.buffer () in
  tv#set_buffer buf;
  buf

let select_obligs (model:GTree.tree_store) (tv:GText.view) (tv_s:GText.view) selected_rows = 
  List.iter
    (fun p ->
       let row = model#get_iter p in
       let s = model#get ~row ~column:Model.fullname in
	 try
	   let o = Model.find_oblig s in
	   let buf = update_buffer tv in
	   buf#set_text "";
	   Pprinter.text_of_obligation tv tv_s o (Astprinter.is_active ());
	   let mark = `MARK (tv#buffer#create_mark tv#buffer#end_iter) in
	   tv#scroll_to_mark ~use_align:true mark
	 with Not_found -> ())
    selected_rows

(* 
 * Timeout 
 *)
let timeout = ref 10
let set_timeout v = timeout := v

(*
 * Default prover
 *)
let default_prover = ref Model.simplify
let set_prover p = default_prover := p
let print_prover p = p.Model.pr_name
let get_prover s = 
  let rec next = function
    | [] -> assert false;
    | p' :: r -> if p'.Model.pr_name = s then p' else next r
  in next Model.provers

let prove fct = 
  ignore (Thread.create fct ())

let update_statistics p (model:GTree.tree_store) row result = 
  let stat = string_of_int result in
  model#set ~row ~column:p.Model.pr_result stat

let get_statistics (model:GTree.tree_store) row = 
  let sl = 
    List.map 
      (fun p -> model#get ~row ~column:p.Model.pr_result) 
      Model.provers 
  in
  "[" ^ String.concat "|" sl ^ "]"
  

let get_all_results f (model:GTree.tree_store) = 
  let mychildren = Model.find_fobligs f in
  Queue.fold
    (fun nb row -> 
       let result = model#get ~row ~column:Model.result in
       result + nb)
    0
    mychildren

(*
 * Should i proove this obligation again ?
 *)
let try_proof oblig =
  (Cache.try_proof ())
  or not (Cache.is_enabled ())
  or (Cache.is_enabled () && not (Cache.o_in_cache oblig)) 

(* 
 * run a prover on an obligation and update the model 
 *)
let run_prover_child p (view:GTree.view) (model:GTree.tree_store) o = 
  let column_p = p.Model.pr_icon in
  let (_, oblig, seq) = o in
  if (try_proof o) then
    try 
      let row = Hashtbl.find Model.orows oblig in
      model#set ~row ~column:column_p `EXECUTE;
      let r = 
	Dispatcher.call_prover ~obligation:oblig ~timeout:!timeout p.Model.pr_id
      in
      let get_result = function
	| Calldp.Valid -> 
	    Cache.add seq p.Model.pr_name;
	    model#set ~row ~column:column_p `YES ; 1
	| Calldp.ProverFailure _ -> model#set ~row ~column:column_p `NO; 0
	| Calldp.Timeout -> model#set ~row ~column:column_p `CUT; 0
	| _ -> model#set ~row ~column:column_p `STOP; 0 in
      let result = get_result r in
      model#set ~row ~column:Model.result 
	(max result (model#get ~row ~column:Model.result));
      result
    with Not_found -> begin
      print_endline ("     [...] Error : obligation \""^oblig^"\" not found !"); 
      flush stdout;
      0
    end
  else begin
    !flash_info "No need to prove these obligations";
    1
  end

let run_prover_oblig p (view:GTree.view) (model:GTree.tree_store) s () = 
  try 
    let oblig = Hashtbl.find Model.obligs s in
    let _ = run_prover_child p view model oblig in
    ()
  with Not_found -> begin
    print_endline ("     [...] Error : obligation \""^s^"\" not found !"); 
    flush stdout;
  end

(*
 * run a prover on a function and update the model 
 *)
let run_prover_fct p (view:GTree.view) (model:GTree.tree_store) f () = 
  let column_p = p.Model.pr_icon in
  try
    let row = Model.find_fct f in
    model#set ~row ~column:Model.total 0;
    model#set ~row ~column:column_p `GO_DOWN;
    let n = model#iter_n_children (Some(row)) in
    let mychildren = Model.find_fobligs f in
    let succeed = 
      Queue.fold
	(fun nb row -> 
	   let s = model#get ~row ~column:Model.fullname in
	   let oblig = Model.find_oblig s in
	   let result = run_prover_child p view model oblig in
	   result + nb)
	0
	mychildren 
    in
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
    update_statistics p model row succeed;
    let statistics = get_statistics model row 
    and total = string_of_int (get_all_results f model) 
    and children = string_of_int n in
    !flash_info 
      ("Function \""^f^"\" statistics : "^statistics^" / "^(string_of_int n));
    model#set 
      ~row ~column:Model.name (f^" "^" "^total^"/"^children^" "^statistics)
  with Not_found -> 
    begin 
      print_endline ("     [...] Error : function \""^f^"\" not found !"); 
      flush stdout 
    end

(*
 * run a prover on all obligations and update the model 
 *)
let run_prover_all p (view:GTree.view) (model:GTree.tree_store) () =
  Queue.iter 
    (fun f -> run_prover_fct p view model f ()) 
    Model.fq

let main () = 
  let w = GWindow.window 
	    ~allow_grow:true ~allow_shrink:true
	    ~width:window_width ~height:window_height 
	    ~title:"gWhy : Easy proof with easy tool" ()
  in
  w#misc#modify_font !general_font;
  (* let accel_group = GtkData.AccelGroup.create () in *)
  let _ = w#connect#destroy ~callback:(fun () -> exit 0) in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  (* Menu *)
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in
  let factory = new GMenu.factory menubar in
  let accel_group = factory#accel_group in
  let file_menu = factory#add_submenu "File" in
  let file_factory = new GMenu.factory file_menu ~accel_group in
  let _ = 
    file_factory#add_image_item ~stock:`REFRESH ~label:"Refresh"
      ~key:GdkKeysyms._R () 
  in
  let _ = file_factory#add_separator () in
  let _ = 
    file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"Quit" 
      ~callback:(fun () -> exit 0) () 
  in
  (* configuration menu *)
  let configuration_menu = factory#add_submenu "Configuration" in
  let configuration_factory = 
    new GMenu.factory configuration_menu ~accel_group 
  in
  let _ =
    configuration_factory#add_image_item ~label:"Customize colors" 
      ~stock:`SELECT_COLOR
      ~callback:(fun () -> !flash_info "Not implemented") () in
  let _ = 
    configuration_factory#add_image_item ~label:"Customize fonts" 
      ~stock:`SELECT_FONT
      ~callback:(fun () -> !flash_info "Not implemented") () in

  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in

  (* left tree of proof obligations *)
  let model = Model.create_model () in
  let scrollview = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:350 ~packing:hp#add1 () in
  let view = GTree.view ~model ~packing:scrollview#add_with_viewport () in
  let _ = view#selection#set_mode `SINGLE in
  let _ = view#set_rules_hint true in
  let vc_provers = View.add_columns ~view ~model in
  let _ = 
    Hashtbl.iter 
      (fun f row -> 
	 let n = model#iter_n_children (Some(row)) in
	 model#set ~row ~column:Model.name (f^" 0/"^(string_of_int n)^" [0|0|0]   "))
      Model.frows in
  (* cache and view menu *)
  let _ = configuration_factory#add_separator ()  in
  let _ = 
    configuration_factory#add_image_item ~key:GdkKeysyms._E 
      ~label:"Expand all" ~callback:(fun () -> view#expand_all ()) () 
  in
  let _ = 
    configuration_factory#add_image_item ~key:GdkKeysyms._C 
      ~label:"Collapse all" ~callback:(fun () -> view#collapse_all ()) () 
  in
  let _ = configuration_factory#add_separator ()  in
  (*let cache_m = configuration_factory#add_radio_item ~active:(Cache.is_enabled ())
    "Cache enabled" in
    let _ = cache_m#event#connect#button_release
    ~callback:(fun ev -> 
    Cache.swap_active (); 
    cache_m#set_active (Cache.is_enabled ());
    false) in
    let ocache_m = configuration_factory#add_radio_item ~active:(Cache.try_proof ()) 
    "Proove saved obligations" in
    let _ = ocache_m#event#connect#button_release
    ~callback:(fun ev -> 
    Cache.prove_obligs (); 
    cache_m#set_active (Cache.try_proof ()); 
    false) in*)
  let _ = configuration_factory#add_image_item ~label:"Clear cache" 
    ~callback:(fun () -> 
		 Cache.clear ();
		 !flash_info "Cache cleared"
	      ) () in 
  (* proof menu *)
  let proof_menu = factory#add_submenu "Proof" in
  let proof_factory = new GMenu.factory proof_menu ~accel_group in 
  let _ = 
    proof_factory#add_image_item ~label:"Prove all obligations" 
      ~key:GdkKeysyms._A 
      ~callback:(fun () -> 
		   prove (run_prover_all !default_prover view model)) () 
  in
  let fct_callback () = 
    List.iter 
      (fun p -> 
	 let row = model#get_iter p in
	 let s = model#get ~row ~column:Model.fullname in 
	 if model#iter_has_child row then
	   prove (run_prover_fct !default_prover view model s)
	 else let name,_ = decomp_name s in 
	 prove (run_prover_fct !default_prover view model name))
      view#selection#get_selected_rows in
  let _ = 
    proof_factory#add_image_item ~label:"Prove selected function" 
      ~key:GdkKeysyms._F ~callback:fct_callback () 
  in
  let oblig_callback () =
    List.iter 
      (fun p -> 
	 let row = model#get_iter p in
	 let s = model#get ~row ~column:Model.fullname in 
	 if model#iter_has_child row then
	   let row = Queue.peek (Model.find_fobligs s) in
	   let s = model#get ~row ~column:Model.fullname in
	   prove (run_prover_oblig !default_prover view model s)
	 else 
	   prove (run_prover_oblig !default_prover view model s))
      view#selection#get_selected_rows in
  let _ = 
    proof_factory#add_image_item ~label:"Prove selected obligation" 
      ~key:GdkKeysyms._O ~callback:oblig_callback () 
  in
  (* menus for povers *)
  let _ = proof_factory#add_separator ()  in
  let provers_m =
    List.map
      (fun p -> 
	 p, 
	 proof_factory#add_check_item ~active:true
	   ~callback:(fun b -> default_prover := p) p.Model.pr_name)
      Model.provers
  in
  let provers_cb = 
    List.map
      (fun (p,m) ->
	 let callback ev =
	   List.iter (fun (p',m') -> m'#set_active (p == p')) provers_m;
	   set_prover p;
	   !flash_info (p.Model.pr_name ^ " selected for default mode");
	   true
	 in
	 m#event#connect#button_release ~callback;
	 p, callback)
    provers_m
  in
  let switch_next_prover () = 
    let current_prover = !default_prover in
    let p1,cb1 = List.hd provers_cb in
    let rec find_next = function
      | [] -> assert false
      | [p',_] -> assert (current_prover == p'); cb1 ()
      | (p',_) :: (_,cb'') :: _ when current_prover == p' -> cb'' ()
      | _ :: r -> find_next r
    in
    ignore (find_next provers_cb)
  in 
  let _ = proof_factory#add_separator ()  in
  let _ = 
    proof_factory#add_image_item ~key:GdkKeysyms._N 
      ~label:"Switch to next prover" ~callback:switch_next_prover () 
  in


  (* run provers on all proof obligations *)
  List.iter
    (fun (p,vc) -> 
       let _ =
	 vc#connect#clicked 
	   ~callback:(fun () -> 
	      prove (run_prover_all p view model))
       in
       ())
    vc_provers;

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

  (* lower text view: source code *)
  let tv2 = GText.view ~packing:(sw2#add) () in
  let _ = tv2#misc#modify_font !lower_view_general_font in
  let _ = tv2#set_editable false in
  let _ = tv2#set_wrap_mode `WORD in

  (* upper text view: obligation *)
  let buf1 = GText.buffer () in 
  let tv1 = GText.view ~buffer:buf1 ~packing:(sw1#add) () in
  let _ = tv1#misc#modify_font !upper_view_general_font in
  let _ = tv1#set_editable false in
  let _ = tv1#set_wrap_mode `WORD in
 
  (* status bar  *)
  let mypprint = GButton.check_button ~label:"Pretty Printer   " ~active:(Cache.is_enabled ()) 
    ~packing:hbox#pack() in
  let _ = mypprint#connect#toggled 
    ~callback:(fun () -> Astprinter.swap_active ();
		 let list = view#selection#get_selected_rows in
		 select_obligs model tv1 tv2 list
	      ) in
  (* cache *)
  let mycache = GButton.check_button ~label:"Cache   " ~active:(Cache.is_enabled ()) 
    ~packing:hbox#pack() in
  let _ = mycache#connect#toggled ~callback:(fun () -> Cache.swap_active ()) in
  let myoblig = GButton.check_button ~label:"Hard Proof   " ~active:(Cache.try_proof ()) 
    ~packing:hbox#pack() in
  let _ = myoblig#connect#toggled ~callback:(fun () -> Cache.swap_try_proof ()) in
  (* timeout set *)
  let _ = GMisc.label ~text:"Timeout" ~xalign:0. ~packing:hbox#pack () in
  let timeout = GEdit.spin_button ~digits:0 ~packing:hbox#pack () in
  timeout#adjustment#set_bounds ~lower:1. ~upper:999. ~step_incr:1. ();
  timeout#adjustment#set_value 10.;
  let _ = 
    timeout#connect#value_changed ~callback:
      (fun () -> set_timeout timeout#value_as_int)
  in

  (* status bar *)
  let status_bar = 
    GMisc.statusbar ~packing:(hbox#pack ~fill:true ~expand:true) () 
  in
  status_bar#misc#modify_font !statusbar_font ;
  let status_context = status_bar#new_context "messages" in
  (*ignore (status_context#push "Welcome to the Why GUI");*)
  display_info := (fun s -> 
		     status_context#pop ();
		     ignore (status_context#push s));
  flash_info := (fun s -> status_context#flash ~delay:2000 s);
  
  (* for text components *)
  let _ = GtkBase.Widget.add_events tv1#as_widget
    [`ENTER_NOTIFY; `POINTER_MOTION] in
  let _ = 
    tv1#event#connect#motion_notify ~callback:
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
       if tags = [] then Tags.reset_last_colored () else
       List.iter 
	 ( fun t ->
	     Tags.reset_last_colored ();
	     ignore (GtkText.Tag.event 
		       t#as_tag
		       tv2#as_widget
		       e 
		       it#as_iter))
	 tags;
       false)
  in
  
  (*
   * obligation selection 
   *)
  let _ =
    view#selection#connect#after#changed ~callback:
      begin fun () ->
	let list = view#selection#get_selected_rows in
        select_obligs model tv1 tv2 list
      end
  in

  (*
   * Running obligation 
   *)
  ignore (view#event#connect#button_release ~callback:
	    (fun ev -> 
	       if GdkEvent.Button.button ev = 3 then 
		 List.iter 
		   (fun p -> 
		      let row = model#get_iter p in
		      let s = model#get ~row ~column:Model.fullname in
		      if model#iter_has_child row then
			prove (run_prover_fct !default_prover view model s)
		      else 
			prove (run_prover_oblig !default_prover view model s)
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

  (* Setting special icons for prooved obligation in cache *)
  let _ = 
    load_cache "/tmp/gwhy.cache";
    if not (Cache.is_empty ()) then 
      Hashtbl.iter 
	(fun s (_,o,seq) -> 
	   let cleaned = Astprinter.clean seq in
	   if in_cache cleaned then
	     begin 
	       let row = Hashtbl.find Model.orows o in
	       try 
		 Queue.iter 
		   (fun p -> 
		      let zecol = get_prover p in
		      model#set ~row ~column:zecol.Model.pr_icon `HARDDISK;
		      model#set ~row ~column:Model.result 1
		   )
		   (Cache.find cleaned)
	       with Not_found -> 
		 begin 
		   print_endline ("sequent not found for "^o);
		   flush stdout
		 end
	     end
	) 
	Model.obligs;
  in
  let _ = (* update statistics for functions *)
    Hashtbl.iter 
    (fun k row -> 
       let success = (string_of_int (get_all_results k model))
       and n = (string_of_int (model#iter_n_children (Some(row))))
       in let s = get_statistics model (Hashtbl.find Model.frows k)
       in model#set ~row ~column:Model.name (k^" "^" "^success^"/"^n^" "^s)
    )
    Model.frows
  in

  (* initialisation for check menus *)
  List.iter
    (fun (p,cb) -> if p == !default_prover then ignore (cb ())) provers_cb;

  w#add_accel_group accel_group;
  w#show ()

(* Main *)
let _ = 
  ignore (GtkMain.Main.init ());
  main () ;
  GtkThread.main ()
