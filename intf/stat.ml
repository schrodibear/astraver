(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

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

(*i $Id: stat.ml,v 1.44 2006-11-03 11:55:26 marche Exp $ i*)

open Printf
open Options
open Ast
open Env
open Cache
open Pprinter

let _ = gui := true
let debug = ref Options.debug

let is_caduceus = 
  List.exists (fun f -> Filename.basename f = "caduceus.why") Options.files 

let get_files fl = 
  let files = List.map (fun f -> Filename.chop_extension (Filename.basename f)) fl 
  in
  List.fold_left
    (fun l f -> 
       let file = (Filename.concat (Sys.getcwd ()) f) ^ ".c" in
       if Sys.file_exists file 
       then file :: l
       else l)
    fl
    files

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

let monospace_font = ref (Pango.Font.from_string "Monospace 10")
let general_font = ref (Pango.Font.from_string "Monospace 10")

let lower_view_general_font = general_font
let upper_view_general_font = general_font
let statusbar_font = ref !general_font
let proved_lemma_font = ref !monospace_font
let to_prove_lemma_font = ref !monospace_font
let discharged_lemma_font = ref !monospace_font
let display_info = ref (function s -> failwith "not ready")
let flash_info = ref (function s -> failwith "not ready")

let cache_check = ref (GButton.toggle_button ())
let hard_proof_check = ref (GButton.toggle_button ())
let pretty_printer_check = ref (GButton.toggle_button ())
let live_update_check = ref (GButton.toggle_button ())
let timeout_spin = ref (GEdit.spin_button ())

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

module View = struct

  open GtkTree
  open Model

  let renderer = GTree.cell_renderer_text [`XALIGN 0.] 
  let first_col = GTree.view_column ~title:"Proof obligations " 
    ~renderer:(renderer, ["text", Model.name]) () 
 

  let add_columns ~(view : GTree.view) ~model =
    (* let renderer = GTree.cell_renderer_text [`XALIGN 0.] in *)
    let icon_renderer = GTree.cell_renderer_pixbuf [ `STOCK_SIZE `BUTTON ] in
    let _ = view#append_column first_col 
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
      (Model.get_provers ())

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
	   Pprinter.text_of_obligation tv o;
	   let mark = `MARK (tv#buffer#create_mark tv#buffer#end_iter) in
	   tv#scroll_to_mark ~use_align:true mark
	 with Not_found -> ())
    selected_rows

let prove fct = 
  ignore (Thread.create fct ())

let update_statistics p (model:GTree.tree_store) row result = 
  model#set ~row ~column:p.Model.pr_result result

let get_statistics (model:GTree.tree_store) row = 
  let sl = 
    List.map 
      (fun p -> (string_of_int (model#get ~row ~column:p.Model.pr_result)))
      (Model.get_provers ())
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

let build_statistics (model:GTree.tree_store) f = 
  try
    let row = Model.find_fct f
    and children = ref 0 in
    List.iter 
      (fun p -> 
	 model#set ~row ~column:p.Model.pr_result 0
      ) 
      (Model.get_provers ());
    Model.iter_fobligs
      f
      (fun r -> 
	 incr children;
	 List.iter 
	   (fun p -> 
	      let r = model#get ~row:r ~column:p.Model.pr_result 
	      and u = model#get ~row ~column:p.Model.pr_result in
	      model#set ~row ~column:p.Model.pr_result (u+r)
	   ) 
	   (Model.get_provers ()));
    let statistics = get_statistics model row 
    and total = string_of_int (get_all_results f model) 
    and children = string_of_int !children in
    model#set 
      ~row ~column:Model.name (f^" "^" "^total^"/"^children^" "^statistics)
  with e -> 
    begin 
      print_endline ("     [...] Error: unexcepted exception: " ^ Printexc.to_string e);
      flush stdout 
    end  

let collapse_row (view:GTree.view) path bench = 
  if not bench then begin
    view#collapse_row path
  end

let expand_row (view:GTree.view) path bench = 
  if not bench then begin
    view#expand_row path
  end

(*
 * Should i proove this obligation again ?
 *)
let try_proof oblig =
  (Cache.hard_proof ())
  or not (Cache.is_enabled ())
  or (Cache.is_enabled () && not (in_cache (Cache.clean oblig))) 

(* 
 * run a prover on an obligation and update the model 
 *)
let run_prover_child p (view:GTree.view) (model:GTree.tree_store) o bench alone = 
  let column_p = p.Model.pr_icon in
  let (_, oblig, seq) = o in
  if bench or (try_proof seq) then
    try 
      let row = 
	try Hashtbl.find Model.orows oblig 
	with Not_found -> 
	  print_endline ("     [...] Error : obligation \""^oblig^"\" not found !"); 
	  flush stdout;
	  raise Exit
      in
      model#set ~row ~column:column_p `EXECUTE;
      let r = 
	Dispatcher.call_prover 
	  ~debug:!debug ~encoding:p.Model.pr_enc
	  ~obligation:oblig ~timeout:(Tools.get_timeout ())  p.Model.pr_id
      in
      let get_result = function
	| Calldp.Valid _ -> 
	    Cache.add seq p.Model.pr_name;
	    model#set ~row ~column:column_p `YES ; 1
	| Calldp.Timeout _ -> model#set ~row ~column:column_p `CUT; 0
	| Calldp.CannotDecide _ -> model#set ~row ~column:column_p `MISSING_IMAGE; 0
	| Calldp.Invalid(_,so) -> 
	    begin
	      (match so with
		| None -> ()
		| Some s -> 
		    let name = model#get ~row ~column:Model.fullname in 
		    Model.add_failure name p s);
	      model#set ~row ~column:column_p `NO; 0
	    end
	| Calldp.ProverFailure so -> 
	    begin
	      let name = model#get ~row ~column:Model.fullname in 
	      Model.add_failure name p so;
	      model#set ~row ~column:column_p `PREFERENCES; 0
	    end 
      in
      let result = get_result r in
      model#set ~row ~column:p.Model.pr_result result;
      model#set ~row ~column:Model.result 
	(max result (model#get ~row ~column:Model.result));
      if alone or (Tools.live_update ())then begin 
	build_statistics model (model#get ~row ~column:Model.parent)
      end;
      result
    with Exit ->
      0
  else begin
    !flash_info "No need to prove these obligations";
    1
  end

let run_prover_oblig p (view:GTree.view) (model:GTree.tree_store) s bench alone () = 
  try 
    let oblig = Hashtbl.find Model.obligs s in
    let _ = run_prover_child p view model oblig bench alone in
    ()
  with Not_found -> begin
    print_endline ("     [...] Error : obligation \""^s^"\" not found !"); 
    flush stdout;
  end

(*
 * run a prover on a function and update the model 
 *)
let run_prover_fct p (view:GTree.view) (model:GTree.tree_store) f bench () = 
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
	   let result = run_prover_child p view model oblig bench false in
	   result + nb)
	0
	mychildren 
    in
    if succeed = n then 
      begin 
	model#set ~row ~column:column_p `APPLY;
	let path = model#get_path row in
	collapse_row view path bench
      end
    else 
      begin 
	model#set ~row ~column:column_p `CANCEL;
	let path = model#get_path row in
	expand_row view path bench
      end;
    if not (Tools.live_update ()) then begin 
      build_statistics model f
    end 
  with Not_found -> 
    begin 
      print_endline ("     [...] Error : function \""^f^"\" not found !"); 
      flush stdout 
    end

(*
 * run a prover on all obligations and update the model 
 *)
let run_prover_all p (view:GTree.view) (model:GTree.tree_store) bench () =
  Queue.iter 
    (fun f -> run_prover_fct p view model f bench ()) 
    Model.fq

let main () = 
  let w = GWindow.window 
	    ~allow_grow:true ~allow_shrink:true
	    ~width:window_width ~height:window_height 
	    ~title:"gWhy : Easy proof with easy tool" ()
  in
  w#misc#modify_font !general_font;
  let _ = w#connect#destroy ~callback:(fun () -> exit 0) in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  (* Menu *)
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in
  let factory = new GMenu.factory menubar in
  let accel_group = factory#accel_group in
  let file_menu = factory#add_submenu "_File" in
  let file_factory = new GMenu.factory file_menu ~accel_group in
  let _ = 
    file_factory#add_image_item (*~stock:`REFRESH*) ~label:"_Refresh"
      ~key:GdkKeysyms._R () 
  in
  let _ = file_factory#add_separator () in
  let _ = 
    file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"_Quit" 
      ~callback:(fun () -> exit 0) () 
  in
  (* configuration menu *)
  let configuration_menu = factory#add_submenu "_Configuration" in
  let configuration_factory = 
    new GMenu.factory configuration_menu ~accel_group 
  in
  let unit () = () in
  let _ =
    configuration_factory#add_item ~key:GdkKeysyms._S
      ~callback:(fun () -> Config.save ()) "Save preferences" in
  let _ =
    configuration_factory#add_item 
      ~callback:(fun () -> Preferences.show Tools.Color unit ()) "Customize colors" in
  (*let ft = 
   * configuration_factory#add_item 
   *   ~callback:(fun () -> !flash_info "Not implemented") "Customize fonts" in
   *)

  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in
  let vtable = GPack.table ~row_spacings:5 ~homogeneous:false ~packing:hp#add () in
  let table = GPack.table ~col_spacings:15 ~homogeneous:false () in
  let _ = vtable#attach ~left:0 ~top:0 table#coerce in

  let model = Model.create_model () in

  (* function list *)
  let files = List.map 
    (fun f -> 
       if Filename.is_relative f 
       then Filename.concat (Sys.getcwd ()) f
       else f)
    Options.files 
  in
  let files_label = GMisc.label ~text:"Opened files" () in
  table#attach ~left:0 ~top:0 files_label#coerce;
  let files_combo = GEdit.combo ~allow_empty:false ~popdown_strings:(get_files files)
    ~value_in_list:true () in
  table#attach ~left:1 ~top:0 ~expand:`BOTH files_combo#coerce;
  let _ = files_combo#entry#set_editable false in
  
  (* left tree of proof obligations *)
  let scrollview = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:400 () in
  let _ = vtable#attach ~left:0 ~top:1 ~expand:`BOTH scrollview#coerce in
  let view = GTree.view ~model ~packing:scrollview#add_with_viewport () in
  let _ = view#selection#set_mode `SINGLE in
  let _ = view#set_rules_hint true in
  let vc_provers = View.add_columns ~view ~model in
  
  (* cache and view menu *)
  let _ = configuration_factory#add_separator () in
  let _ = 
    configuration_factory#add_image_item ~key:GdkKeysyms._E 
      ~label:"Expand all" ~callback:(fun () -> view#expand_all ()) () 
  in
  let _ = 
    configuration_factory#add_image_item ~key:GdkKeysyms._C 
      ~label:"Collapse all" ~callback:(fun () -> view#collapse_all ()) () 
  in
  let _ = 
    configuration_factory#add_image_item ~key:GdkKeysyms._Z 
      ~label:"Expand function" 
      ~callback:(fun () -> match view#selection#get_selected_rows with
		   | [] -> ()
		   | p::_ -> 
		       let iter = model#get_iter p in
		       try 
			 let parent = model#get ~row:iter ~column:Model.parent in
			 let row = model#get_path (Hashtbl.find Model.frows parent) in
			 view#expand_row row
		       with Not_found -> ()) () 
  in
  let _ = 
    configuration_factory#add_image_item ~key:GdkKeysyms._X 
      ~label:"Collapse function" 
      ~callback:(fun () -> match view#selection#get_selected_rows with
		   | [] -> ()
		   | p::_ -> 
		       let iter = model#get_iter p in
		       try 
			 let parent = model#get ~row:iter ~column:Model.parent in
			 let row = model#get_path (Hashtbl.find Model.frows parent) in
			 view#collapse_row row
		       with Not_found -> ()) () 
  in
  (* menus for selected povers *)
  let _ = configuration_factory#add_separator ()  in
  let _ = 
    List.iter
      (fun p -> 
	 let m = configuration_factory#add_check_item 
	   ~active:(List.mem p (Model.get_provers ())) p.Model.pr_name
	 in 
	 ignore(m#connect#toggled  
		  ~callback:(fun () -> 
			       if m#active then 
				 Model.select_prover p
			       else Model.deselect_prover p)))
      Model.provers
  in 
  let _ = configuration_factory#add_separator ()  in
  let cache = configuration_factory#add_check_item 
    ~callback:(fun b -> Cache.set_active b) "Cache _enabled" in
  let _ = cache#set_active (Cache.is_enabled ()) in
  let _ = configuration_factory#add_image_item ~label:"Clear cache" 
    (*~stock:`CLEAR*) ~key:GdkKeysyms._K
    ~callback:(fun () -> 
		 Cache.clear ();
		 !flash_info "Cache cleared"
	      ) () 
  in 
  
  (* proof menu *)
  let proof_menu = factory#add_submenu "_Proof" in
  let proof_factory = new GMenu.factory proof_menu ~accel_group in 
  let _ = 
    proof_factory#add_image_item ~label:"Start _benchmark" 
      ~key:GdkKeysyms._B 
      ~callback:(fun () -> 
		   List.iter
		     (fun p -> prove (run_prover_all p view model true))
		     (Model.get_provers ())) () 
  in
  let fct_callback bench () = 
    List.iter 
      (fun p -> 
	 let row = model#get_iter p in
	 let s = model#get ~row ~column:Model.fullname in 
	 if model#iter_has_child row then
	   prove (run_prover_fct (Model.get_default_prover ()) view model s bench)
	 else let name = model#get ~row ~column:Model.parent in 
	 prove (run_prover_fct (Model.get_default_prover ()) view model name bench))
      view#selection#get_selected_rows 
  in
  let _ = 
    proof_factory#add_image_item ~label:"Start benchmark _on selected function" 
      ~key:GdkKeysyms._P 
      ~callback:(fun () -> 
		   let row = model#get_iter (List.hd view#selection#get_selected_rows) in
		   let s = 
		     if model#iter_has_child row 
		     then model#get ~row ~column:Model.fullname 
		     else model#get ~row ~column:Model.parent
		   in
		   List.iter
		     (fun p -> prove (run_prover_fct p view model s true))
		     (Model.get_provers())) ()
  in
  let _ = 
    proof_factory#add_image_item ~label:"Prove _all obligations" 
      ~key:GdkKeysyms._A 
      ~callback:(fun () -> 
		   prove (run_prover_all (Model.get_default_prover ()) view model false)) () 
  in
  let _ = 
    proof_factory#add_image_item ~label:"Prove selected _function" 
      ~key:GdkKeysyms._F ~callback:(fct_callback false) ()
  in
  let oblig_callback () =
    List.iter 
      (fun p -> 
	 let row = model#get_iter p in
	 let s = model#get ~row ~column:Model.fullname in 
	 (if model#iter_has_child row then
	    let row = Queue.peek (Model.find_fobligs s) in
	    let s = model#get ~row ~column:Model.fullname in
	    prove (run_prover_oblig (Model.get_default_prover ()) view model s false true)
	  else 
	    prove (run_prover_oblig (Model.get_default_prover ()) view model s false true));
      )
      view#selection#get_selected_rows in
  let _ = 
    proof_factory#add_image_item ~label:"Prove selected _obligation" 
      ~key:GdkKeysyms._O ~callback:oblig_callback () 
  in
  (* menus for povers *)
  let _ = proof_factory#add_separator ()  in
  let select_prover p = 
    (try !flash_info (p.Model.pr_name ^" selected for default mode !")
    with _ -> ());
    Model.set_prover p
  in
  let provers_m = 
    let name = (Model.get_default_prover ()).Model.pr_name
    and pp = List.hd (Model.get_provers ()) in
    let fm = proof_factory#add_radio_item ~active:(name = pp.Model.pr_name) 
      pp.Model.pr_name in
    ignore(fm#connect#toggled  
	     ~callback:(fun () -> select_prover pp));
    let group = fm#group in
    (pp, fm) :: List.map
      (fun p -> 
	 let m = proof_factory#add_radio_item 
	   ~active:(name = p.Model.pr_name) ~group p.Model.pr_name 
	 in ignore(m#connect#toggled  
		     ~callback:(fun () -> select_prover p));
	 p,m)
      (List.tl (Model.get_provers ()))
  in 
  let switch_next_prover () =     
    let current_prover = Model.get_default_prover () in
    let rec find_next = function
      | [] -> assert false
      | [p',_] -> 
	  assert (current_prover == p'); 
	  let prems = (List.hd provers_m) in
	  select_prover (fst prems);
	  (snd prems)#set_active true
      | (p',_) :: (p'',m) :: _ when current_prover == p' -> 
	  select_prover p'';
	  m#set_active true
      | _ :: r -> find_next r
    in
    ignore (find_next provers_m)
  in 
  let _ = proof_factory#add_separator ()  in
  let _ = 
    proof_factory#add_image_item ~key:GdkKeysyms._N 
      ~label:"_Switch to next prover" ~callback:switch_next_prover () 
  in
  let _ = proof_factory#add_separator () in
  let hardproof = proof_factory#add_check_item 
    ~callback:(fun b -> Cache.set_hard_proof b) "_Hard proof" in
  let _ = hardproof#set_active (Cache.hard_proof ()) in
  let liveupd = proof_factory#add_check_item 
    ~callback:(fun b -> Tools.set_live b) "_Live update" in
  let _ = liveupd#set_active (Tools.live_update ()) in
  let debugd = proof_factory#add_check_item 
    ~callback:(fun b -> debug := b) "_Debug mode" in
  let _ = debugd#set_active !debug in

  (* run provers on all proof obligations *)
  List.iter
    (fun (p,vc) -> 
       let _ =
	 vc#connect#clicked 
	   ~callback:(fun () -> 
	      prove (run_prover_all p view model false))
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
  let _ = Pprinter.set_tvsource tv2 in

  (* upper text view: obligation *)
  let buf1 = GText.buffer () in 
  let tv1 = GText.view ~buffer:buf1 ~packing:(sw1#add) () in
  let _ = tv1#misc#modify_font !upper_view_general_font in
  let _ = tv1#set_editable false in
  let _ = tv1#set_wrap_mode `WORD in
 
  (* timeout set *)
  let _ = GMisc.label ~text:" Timeout" ~xalign:0. ~packing:hbox#pack () in
  let timeout_b = GEdit.spin_button ~digits:0 ~packing:hbox#pack () in
  timeout_spin := timeout_b;
  timeout_b#adjustment#set_bounds ~lower:1. ~upper:999. ~step_incr:1. ();
  timeout_b#adjustment#set_value (float_of_int (Tools.get_timeout ()));
  let _ = 
    timeout_b#connect#value_changed ~callback:
      (fun () -> Tools.set_timeout timeout_b#value_as_int)
  in
  (* pretty printer  *)
  let mypprint = GButton.check_button ~label:"Pretty Printer | " 
    ~active:(Pprinter.is_active ()) ~packing:hbox#pack() in
  let _ = mypprint#connect#toggled 
    ~callback:(fun () -> Pprinter.swap_active ();
		 let list = view#selection#get_selected_rows in
		 if list = [] then 
		   !flash_info "No row selected" 
		 else select_obligs model tv1 tv2 list
	      ) in

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
   * function selection 
   *)
  let _ =
    files_combo#entry#event#connect#after#focus_in ~callback:
      begin fun ev -> 
	let s = files_combo#entry#text in
	let loc = {Tags.file=s; Tags.line="1"; Tags.sp="1"; Tags.ep="1"} in
	Pprinter.move_to_source (Some(loc));
	Pprinter.reset_last_file ();
	false
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
		      (if model#iter_has_child row then
			prove (run_prover_fct (Model.get_default_prover ()) view model s false)
		      else 
			prove (run_prover_oblig (Model.get_default_prover ()) view model s false true));
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
   * Obligations : failed with ...
   *)
  ignore (tv2#event#connect#button_release ~callback:
	    (fun ev -> if (GdkEvent.Button.button ev) = 3 then 
	       (match view#selection#get_selected_rows with
		  | [] -> ()
		  | p::_ ->
		      let row = model#get_iter p in
		      if not (model#iter_has_child row) then
			try
			  let name = model#get ~row ~column:Model.fullname in
			  let failed_with = Hashtbl.find Model.fwrows name 
			  and buffer = Buffer.create 1024 in
			  Hashtbl.iter
			    (fun p m -> Buffer.add_string buffer (p.Model.pr_name ^ ": \n" ^ m ^" \n\n"))
			    failed_with;
			  let tbuf = GText.buffer () in
			  tv2#set_buffer tbuf;
			  tbuf#set_text (Buffer.contents buffer);
			  Pprinter.reset_last_file ();
			  Buffer.clear buffer
			with Not_found -> ()); 
	       false));

  (*
   * Startup configuration 
   *)
  (* shows first obligation *)
  let _ = 
    match !Model.first_row with
      | None -> () 
      | Some row -> 
	  let path = model#get_path row in
	  view#selection#select_path path;
	  select_obligs model tv1 tv2 [path]; 
  in

  (* Setting special icons for prooved obligation in cache *)
  let _ = 
    load_cache "gwhy.cache";
    if not (Cache.is_empty ()) then 
      Hashtbl.iter 
	(fun s (_,o,seq) -> 
	   let cleaned = Cache.clean seq in
	   if in_cache cleaned then
	     begin 
	       let row = Hashtbl.find Model.orows o in
	       try 
		 Queue.iter 
		   (fun p -> 
		      try 
			let zecol = Model.get_prover p 
			and parent = model#get ~row ~column:Model.parent in
			let parent = Model.find_fct parent in
			let r = model#get ~row:parent ~column:zecol.Model.pr_result in
			model#set ~row ~column:zecol.Model.pr_icon `HARDDISK;
			model#set ~row ~column:zecol.Model.pr_result 1;
			model#set ~row ~column:Model.result 1;
			model#set ~row:parent ~column:zecol.Model.pr_result (r+1)
		      with Model.No_such_prover -> ()
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
  w#add_accel_group accel_group;
  w#show ()

(* config in .gwhyrc *)
let set_loaded_config () = 
  let l = [("cache", Cache.set_active) ; 
	   ("hard_proof", Cache.set_hard_proof) ; 
	   ("live_update", Tools.set_live)] in
  List.iter 
    (fun (k,f) -> 
       let v = 
	 try bool_of_string (Config.get_value k)
	 with _ -> begin
	   prerr_endline ("     [...] .gwhyrc : invalid value for " ^ k); 
	   true 
	 end
	 in
       (f v))
    l;
  Tools.set_timeout 
    (try (int_of_string (Config.get_value "timeout"))
     with _ -> 
       begin
	 prerr_endline ("     [...] .gwhyrc : invalid value for timeout"); 
	 10 
       end);
  Model.set_prover 
    (try (Model.get_prover (Config.get_value "prover"))
    with Model.No_such_prover -> 
      begin
	prerr_endline ("     [...] .gwhyrc : invalid value for prover"); 
	List.hd (Model.get_provers ())
      end);
  Colors.set_all_colors (Config.get_colors ())

(* Main *)
let _ = 
  ignore (GtkMain.Main.init ());
  Config.create_default_config ();
  Config.load ();
  set_loaded_config ();
  if not is_caduceus then Pprinter.desactivate ();
  main () ;
  GtkThread.main ()
