
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
  c_file := Filename.check_suffix f ".c";
  let parsef = if !c_file then Main.c_parser else Main.ml_parser in
  let p = parsef cin in
  if parse_only then exit 0;
  List.iter Main.interp_decl p;
  typed_progs := (f, List.rev !Main.typed_progs) :: !typed_progs;
  close_in cin

let _ =
  try
    List.iter deal_file Options.files
  with e ->
    Main.explain_exception err_formatter e;
    pp_print_newline err_formatter ();
    exit 1

module Tree = struct

  type t = typed_program
	     
  type info = Loc.t * string

  let info = 
    let buf = Buffer.create 1024 in
    let fmt = formatter_of_buffer buf in
    fun x -> 
      fprintf fmt "%a@." Util.print_type_c x.info.kappa;
      let s = Buffer.contents buf in
      Buffer.reset buf;
      x.info.loc, s

  let show_info_ref = ref (fun i -> ())
  let show_info i = !show_info_ref i

  let rec statements = function
    | [] -> []
    | Statement x :: bl -> x :: statements bl
    | _ :: bl -> statements bl

  let children x = match x.desc with
    | Seq bl -> statements bl
    | If (e1, e2, e3) -> [e1; e2; e3]
    | Aff (_, e) -> [e]
    | App (e1, Term e2, _) -> [e2; e1]
    | App (e1, _, _) -> [e1]
    | While (e1, _, _, e2) -> [e1; e2]
    | _ -> []

end

module NavTree = Navig.MakeNavTree(Tree)
module Nav = Navig.MakeNavigator(NavTree)


let window_width = 800
let window_height = 900
let show_discharged = ref false

let monospace_font = ref (Pango.Font.from_string "Monospace 15")
let general_font = ref (Pango.Font.from_string "Sans bold 15")

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


let to_refresh reference e = 
  let n = Filename.chop_extension reference ^ e in
  not (Sys.file_exists n) ||
  ((Unix.stat reference).Unix.st_mtime > (Unix.stat n).Unix.st_mtime)

open Hilight

let user_text = ref ([] : Hilight.token list)

let load_source file = 
  try
    let ic = open_in_bin file in 
    let lb = Lexing.from_channel ic in
    let s = 
      if Filename.check_suffix file ".c" 
      then Hilight.next_code_c lb else Hilight.next_code lb
    in
    close_in ic;
    user_text := s
  with _ -> 
    !flash_info ("couldn't load " ^ file);
    user_text := []

let rec insert_user_annotation
  (tb:GText.buffer) (output:GText.buffer) s it 
  (old_tag_props,new_tag_props) (infos,message) =
  let new_tag = tb#create_tag new_tag_props in
  ignore 
    (new_tag#connect#event
       ~callback:
       (fun ~origin:o ev it -> 
	  match GdkEvent.get_type ev with 
	    | `MOTION_NOTIFY -> 
		output#set_text "";
		List.iter (function x -> output#insert x)
		infos;
		!display_info message
	    | _ -> ()));
  tb#insert ~tags:[new_tag] ~iter:it s

let insert_chunk (tb:GText.buffer) (output:GText.buffer) c = match c with
  | Code s -> tb#insert (try_convert s)
  | Annotation s ->
      let t = tb#end_iter in
      insert_user_annotation tb output (try_convert s) t
	([`BACKGROUND "darkgreen"],
	 [`FOREGROUND "darkgreen"])
	([],"User obligation")
 
let create_mark_at (tb:GText.buffer) pos =
  tb#create_mark (tb#get_iter_at_char pos)

let insert_obligations (tb:GText.buffer) (output:GText.buffer) 
  (obligations:Log.t) =
  let marks =
    List.map 
      (function (pos,_,_) as o ->  `MARK (create_mark_at tb pos),o ) 
      obligations
  in 
  ()

let analyze_all (b:GText.buffer) (tb2:GText.buffer) =
  load_source (fst (List.hd !typed_progs));
  b#set_text "";  
  tb2#set_text "";
  List.iter (insert_chunk b tb2) !user_text

let main () = 

  let w = GWindow.window 
	    ~allow_grow:true ~allow_shrink:true
	    ~width:window_width ~height:window_height ~title:"Why viewer" ()
  in
    w#misc#modify_font !general_font;
    let accel_group = GtkData.AccelGroup.create () in
    let _ = w#connect#destroy ~callback:(fun () -> exit 0) in
    let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in
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
    let show_discharged_m = configuration_factory#add_check_item 
			      "Show discharged proof" 
			      ~key:GdkKeysyms._D
			      ~callback:(fun b -> show_discharged := b) 
    in
    let customize_colors_m =
      configuration_factory#add_item "Customize colors"
	~callback:(fun () -> !flash_info "Not implemented")
    in
    let customize_fonts_m = 
      configuration_factory#add_item "Customize fonts"
	~callback:(fun () -> !flash_info "Not implemented")
    in
    let hb = GPack.paned `VERTICAL  ~border_width:3 ~packing:vbox#add () in
    let _ = hb#misc#connect#realize
	      ~callback:(fun _ ->hb#set_position (window_height*6/10 ) ) in
    let _ = hb#set_position (window_height*9/10 ) in
    let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add1 () in 
    let sw1 = GBin.scrolled_window
		~vpolicy:`AUTOMATIC 
		~hpolicy:`AUTOMATIC
		~packing:fr1#add () in
    let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add2 () in 
    let sw2 = GBin.scrolled_window 
		~vpolicy:`AUTOMATIC 
		~hpolicy:`AUTOMATIC
		~packing:(fr2#add) () in
    let status_bar = GMisc.statusbar ~packing:vbox#pack () in
      status_bar#misc#modify_font !statusbar_font ;
      let status_context = status_bar#new_context "messages" in
	ignore (status_context#push "Ready");
	ignore (status_context#push "Ready");
	display_info := (fun s -> 
			   status_context#pop ();
			   ignore (status_context#push s));
	flash_info := !display_info (* fun s -> status_context#flash ~delay:10 s *);
	let tv2 = GText.view ~packing:(sw2#add) () in
	let _ = tv2#misc#modify_font !lower_view_general_font in
	let _ = tv2#set_editable false in
	let tb2 = tv2#buffer in

	let buf1 = GText.buffer () in 
	let tv1 = GText.view ~buffer:buf1 ~packing:(sw1#add) () in
	let _ = tv1#misc#modify_font !upper_view_general_font in
	let _ = tv1#set_editable false in
	let _ = GtkBase.Widget.add_events tv1#as_widget [`POINTER_MOTION] in
	let _ = tv1#event#connect#motion_notify
		  ~callback:(fun e -> 
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
						 tv1#as_widget
						 e 
						 it#as_textiter))
				   tags;
				 false)
	in

(* hook for navigator *)
	let bgtag = buf1#create_tag [`BACKGROUND "light blue"] in
	Tree.show_info_ref := 
  	  (fun ((b,e),s) -> 
	     buf1#remove_tag bgtag ~start:buf1#start_iter ~stop:buf1#end_iter;
	     buf1#apply_tag bgtag 
	     ~start:(buf1#get_iter (`OFFSET b)) 
	     ~stop:(buf1#get_iter (`OFFSET e));
	     buf1#place_cursor (buf1#get_iter (`OFFSET b));
	     tv1#scroll_to_mark ~use_align:true ~yalign:0.25 `INSERT;
	     tb2#set_text s
	  );

	let _ = file_factory#add_item "Up" ~key:GdkKeysyms._Up
		   ~callback:Nav.up in
	let _ = file_factory#add_item "Down" ~key:GdkKeysyms._Down
		   ~callback:Nav.down in
	let _ = file_factory#add_item "Left" ~key:GdkKeysyms._Left
		   ~callback:Nav.left in
	let _ = file_factory#add_item "Right" ~key:GdkKeysyms._Right
		   ~callback:Nav.right in
	let _ = file_factory#add_item "Next" ~key:GdkKeysyms._space
		   ~callback:Nav.next in


	  buf1#place_cursor ~where:buf1#start_iter;
	  let _ =  refresh_m#connect#activate 
		   ~callback:(fun () -> analyze_all buf1 tb2) 
	  in
	    w#add_accel_group accel_group;

	    (* Remove default pango menu for textviews *)
	    ignore (tv1#event#connect#button_press ~callback:
		      (fun ev -> true or GdkEvent.Button.button ev = 3));
	    ignore (tv2#event#connect#button_press ~callback:
		      (fun ev -> true or GdkEvent.Button.button ev = 3));

	    w#show ();
	    analyze_all buf1 tb2;

	    Nav.set (NavTree.create (List.hd (snd (List.hd !typed_progs))))



let _ = 
  ignore (GtkMain.Main.init ());
  main () ;
  GMain.Main.main ()
