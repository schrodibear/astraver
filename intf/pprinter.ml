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
let last_fct = ref ""
let last_line = ref 0
let last_file = ref ""
let pwd = Sys.getcwd ()
let source = ref ""
let tbuf_source = ref (GText.buffer ())
let tv_source = ref (GText.view ())

let unicode_sym s = s

let print_loc = function 
  | None -> "\"nowhere\""
  | Some {file=f; line=l; sp=s; ep=e} ->
      let ff = Filename.concat pwd f in
      ("file \""^ff^"\", line "^l^", characters "^s^" - "^e)

let read_file = function 
  | None -> ()
  | Some {file=f; line=l; sp=_; ep=_} ->
      try
	let in_channel = open_in f in
	let content = ref "" in
	try
          let lexbuf = Lexing.from_channel in_channel in
          while true do
            Hilight.token !tbuf_source lexbuf;
          done
	with Hilight.Eof -> ()
      with Sys_error s -> 
	begin
	  print_endline ("     [...] Sys_error : "^s); flush stdout;
	  !tbuf_source#set_text "" 
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
      if !last_file = file && !last_line <> line then begin
	last_line := line;
	move_to_line line
      end
      else if !last_file <> file then begin
	last_file := file;
	last_line := line;
	read_file (Some(loc));
	move_to_line line
      end

let rec intros ctx = function 
  | Forall (true, id, n, t, p) ->
      let id' = Ident.next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      let ctx', concl' = intros (Svar (id', TTpure t) :: ctx) p' in
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
	   Tags.refresh_last_colored new_tag;
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
	fprintf fmt "@[@{<var>%a:@}@ @{<cc_type>%a@}@]" Ident.print id print_cc_type t
    | Spred (id, p) ->
	fprintf fmt "@[@{<hypothesis>%a:@} @{<predicate>%a@}@]" print_name id print_predicate p
  in
  print_list (print_hyp fmt) ctx
  (*fprintf fmt "@{<separator>%s@\n@}@[@{<conclusion>%a@}@]" "-------------" print_predicate concl*)

let is_buffer_saved = 
  Hashtbl.mem obligs

let save_buffer s (tbuf:GText.buffer) = 
  Hashtbl.add obligs s tbuf

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
  tbuf#insert ~tags:[mytag] ~iter:tbuf#end_iter "_                                                        _\n\n";
  let conclusion = 
    fprintf fmt "@[@{<conclusion>%a@}@]" print_predicate concl;
    create_all_tags tbuf;
    flush_str_formatter () in
  split tbuf (Lexing.from_string conclusion)

let text_of_obligation (tv:GText.view) (tv_s:GText.view) (o,s,p) = 
  tbuf_source := tv_s#buffer;
  tv_source := tv_s;
  last_fct := s;
  if (is_buffer_saved s) then 
    tv#set_buffer (get_buffer s)
  else begin
    let tbuf = GText.buffer () in
    tv#set_buffer tbuf;
    print_all tbuf s p;
    save_buffer s tbuf;
  end
