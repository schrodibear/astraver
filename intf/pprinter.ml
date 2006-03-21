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

open Options
open Misc
open Vcg
open Logic
open Cc
open Format
open Astprinter
open Colors
open Tagsplit
open Tags

let obligs = Hashtbl.create 5501 (* Nombre premier de Sophie Germain *)
let pprinter = Hashtbl.create 5501
let files = Hashtbl.create 10
let last_fct = ref ""
let last_line = ref 0
let last_file = ref ""
let pwd = Sys.getcwd ()
let source = ref ""
let tv_source = ref (GText.view ())

let print_loc = function 
  | None -> "\"nowhere\""
  | Some {file=f; line=l; sp=s; ep=e} ->
      let ff = if Filename.is_relative f then Filename.concat pwd f else f in
      ("file \""^ff^"\", line "^l^", characters "^s^" - "^e)

let is_cfile f = Filename.check_suffix f ".c"
  (* otherwise it's .why *)

let read_file = function 
  | None -> ()
  | Some {file=f; line=l; sp=_; ep=_} ->
      try
	let in_channel = open_in f in
	begin 
	  try
            let lexbuf = Lexing.from_channel in_channel 
	    and hilight = if (is_cfile f) then 
	      Hilight.token
	  else Whyhilight.scan in
            while true do
              hilight !tv_source#buffer lexbuf;
            done
	  with Hilight.Eof | Whyhilight.Eof -> ()
	end;
      with Sys_error s -> 
	begin
	  print_endline ("     [...] Sys_error : "^s); flush stdout;
	  !tv_source#buffer#set_text "" 
	end

let hypo = (* Model : HW_11 *)
  let r_hyp = Str.regexp "\\HW_\\([0-9]+\\)" in
  fun s ->
    if Str.string_match r_hyp s 0 then
      (Str.matched_group 1 s)
    else
      s

let hypothesis s = 
  "H"^(hypo s)

let grab_infos = 
  let r_loc = Str.regexp "File \"\\(.+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)" in
  fun s -> 
    if Str.string_match r_loc s 0 then 
      let source = Filename.concat pwd (Str.matched_group 1 s) in
      Some({file=source;
            line=(Str.matched_group 2 s);
            sp=(Str.matched_group 3 s);
            ep=(Str.matched_group 4 s)})
    else None
      
let is_localised = function 
  | None -> false
  | Some _ -> true

let move_to_line line = 
  if line <= !tv_source#buffer#line_count && line <> 0 then begin
    let it = !tv_source#buffer#get_iter (`LINE line) in 
    let mark = `MARK (!tv_source#buffer#create_mark it) 
    and y = if !tv_source#buffer#line_count < 20 then 0.23 else 0.1 in
    !tv_source#scroll_to_mark ~use_align:true ~yalign:y mark;
    if debug then
      begin 
	print_endline ("     [...] Moving to line n "^(string_of_int line)); 
	flush stdout 
      end
  end

let move_to_source = function
  | None -> ()
  | Some loc ->
      let line = int_of_string loc.line
      and file = loc.file in
      last_line := line;
      if !last_file = file then 
	  move_to_line line
      else 
	begin 
	  last_file := file;
	  if (Hashtbl.mem files file) then 
	    !tv_source#set_buffer (Hashtbl.find files file)
	  else  
	    begin
	      !tv_source#set_buffer (GText.buffer ());
	      read_file (Some(loc));
	      Hashtbl.add files file !tv_source#buffer;
	    end;
	  move_to_line line
	end

let rec intros ctx = function 
  | Forall (true, id, n, t, p) ->
      let id' = Ident.next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      let ctx', concl' = intros (Svar (id', t) :: ctx) p' in
      ctx', concl'
  | Pimplies (true, a, b) -> 
      let h = fresh_hyp () in 
      let ctx', concl' = intros (Spred (h, a) :: ctx) b in
      ctx', concl'
  | c -> 
      ctx, c

let create_tag (tbuf:GText.buffer) t loc = 
  let (fc, bc) = get_color "lpredicate" in
  let new_tag = tbuf#create_tag [`BACKGROUND bc; `FOREGROUND fc] in
  ignore(
    new_tag#connect#event ~callback:
      (fun ~origin ev it -> 
	 if GdkEvent.get_type ev = `BUTTON_PRESS then 
	   move_to_source (Some(loc))
	 else if GdkEvent.get_type ev = `MOTION_NOTIFY then begin
	   Tags.refresh_last_colored [new_tag];
	   new_tag#set_properties 
	       [`BACKGROUND bc_hilight; `FOREGROUND fc_hilight]
	 end;
	 false)
  );
  add_gtktag t new_tag

let create_all_tags (tbuf:GText.buffer) = 
  Hashtbl.iter (create_tag tbuf) Tags.loctags

let print_oblig fmt (ctx,concl) = 
  let ctx, concl = intros ctx concl in
  let rec print_list print = function
      | [] -> ()
      | p::r ->
	  print p;
	  fprintf fmt "@\n";
	  print_list print r 
  and print_name fmt id = 
    let hypo_nb = hypo (Ident.string id) in
    fprintf fmt "%s" (hypothesis hypo_nb)
  and print_hyp fmt = function
    | Svar (id, t) ->
	fprintf fmt "@[@{<var>%a:@}@ @{<cc_type>%a@}@]" Ident.print id print_pure_type t
    | Spred (id, p) ->
	fprintf fmt "@[@{<hypothesis>%a:@} @{<predicate>%a@}@]" print_name id print_predicate p
  in
  print_list (print_hyp fmt) ctx

let is_buffer_saved = 
  Hashtbl.mem obligs

let save_buffer s (tbuf:GText.buffer) pprint = 
  Hashtbl.add obligs s tbuf;
  Hashtbl.add pprinter s pprint

let get_buffer = 
  Hashtbl.find obligs
  
let print_all (tbuf:GText.buffer) s p = 
  insert_text tbuf "title" (s^"\n\n");
  let fmt = Format.str_formatter in
  pp_set_tags fmt true;
  let str = 
    fprintf fmt "@[%a@]" print_oblig p;
    flush_str_formatter ()
  in
  create_all_tags tbuf;
  split tbuf (Lexing.from_string str);
  let (_,concl) = p in
  let mytag = tbuf#create_tag [`UNDERLINE `DOUBLE;`FOREGROUND (get_fc "separator")] in
  tbuf#insert ~tags:[mytag] ~iter:tbuf#end_iter 
    "_                                                        _\n\n";
  let conclusion = 
    fprintf fmt "@[@{<conclusion>%a@}@]" print_predicate concl;
    create_all_tags tbuf;
    flush_str_formatter () in
  split tbuf (Lexing.from_string conclusion)

let unchanged s pprint = 
  (is_buffer_saved s) 
  && (try 
	(Hashtbl.find pprinter s) = pprint
      with Not_found -> pprint)

let is_ident_char s = String.length s = 1 && match s.[0] with
  | 'a'..'z' | 'A'..'Z' | '_' | '0'..'9' -> true
  | _ -> false

let show_definition (tv:GText.view) (tv_s:GText.view) = 
  let buf = tv#buffer in
  let find_backward (it:GText.iter) = 
    let rec find start stop = 
      if (start = buf#start_iter) then
	start 
      else
	let c = buf#get_text ~start ~stop () in
	if is_ident_char c then 
	  find (start#backward_char) start
	else stop
    in find (it#backward_char) it
  in
  let find_forward (it:GText.iter) = 
    let rec find start stop = 
      if (stop = buf#end_iter) then
	stop
      else
	let c = buf#get_text ~start ~stop () in
	if is_ident_char c then 
	  find stop (stop#forward_char) 
	else start
    in find it (it#forward_char)
  in
  let buf = tv#buffer in
  let win = match tv#get_window `WIDGET with
    | None -> assert false
    | Some w -> w
  in
  let x,y = Gdk.Window.get_pointer_location win in
  let b_x,b_y = tv#window_to_buffer_coords ~tag:`WIDGET ~x ~y in
  let it = tv#get_iter_at_location ~x:b_x ~y:b_y in
  let start = if (it = buf#start_iter) then it else find_backward it in
  let stop = if (it = buf#end_iter) then it else find_forward it in
  let text = buf#get_text ~start ~stop () in
  if start <> stop && text <> "" then begin
    try 
      let pos = fst (Loc.ident text) in
      let loc = {file=pos.Lexing.pos_fname; 
		 line=(string_of_int pos.Lexing.pos_lnum); 
		 sp=(string_of_int pos.Lexing.pos_bol); 
		 ep=(string_of_int pos.Lexing.pos_cnum)} 
      in 
      (*
       * print_endline (text ^ "  " ^ (print_loc (Some(loc)))); 
       * flush stdout;
       *)
      move_to_source (Some(loc))
    with Not_found -> ()
  end
    
let text_of_obligation (tv:GText.view) (tv_s:GText.view) (o,s,p) pprint = 
  tv_source := tv_s;
  last_fct := s;
  if (unchanged s pprint) then 
    tv#set_buffer (get_buffer s)
  else begin
    let tbuf = GText.buffer () in
    tv#set_buffer tbuf;
    let _ = 
      tv#event#connect#button_release 
	~callback:(fun ev -> 
		     if GdkEvent.Button.button ev = 3 then
		       show_definition tv tv_s; 
		     false)
    in
    print_all tbuf s p;
    save_buffer s tbuf pprint;
  end
