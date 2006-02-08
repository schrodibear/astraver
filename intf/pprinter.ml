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

open Misc
open Vcg
open Logic
open Cc
open Format
open Astprinter

type loc = { file:string; line:string; sp:string; ep:string }

let fcolors = Hashtbl.create 13
let bcolors = Hashtbl.create 13
let obligs = Hashtbl.create 5501 (* Nombre premier de Sophie Germain *)
let last_fct = ref ""
let last_line = ref 0
let last_file = ref ""
let last_colored = ref (GText.tag ())
let pwd = Sys.getcwd ()
let source = ref ""
let tbuf_source = ref (GText.buffer ())
let tv_source = ref (GText.view ())

let _ = 
  Hashtbl.add fcolors "title" "brown";
  Hashtbl.add fcolors "comment" "blue";
  Hashtbl.add fcolors "keyword" "green";
  Hashtbl.add fcolors "var" "darkgreen";
  Hashtbl.add fcolors "predicate" "blue";
  Hashtbl.add fcolors "lpredicate" "blue";
  Hashtbl.add fcolors "information" "orange";
  Hashtbl.add fcolors "separator" "red";
  Hashtbl.add fcolors "hypothesis" "orange";
  Hashtbl.add fcolors "conclusion" "red";
  Hashtbl.add fcolors "highlight" "black"

let _ = 
  Hashtbl.add bcolors "title" "lightgreen";
  Hashtbl.add bcolors "lpredicate" "lightyellow";
  Hashtbl.add bcolors "highlight" "yellow"

let fc_highlight = "red"
let bc_highlight = "lightgreen"

let get_color ty = 
  (try Hashtbl.find fcolors ty with Not_found -> "black") , 
  (try Hashtbl.find bcolors ty with Not_found -> "white")

let get_fc_predicate = 
  (try Hashtbl.find fcolors "lpredicate" with Not_found -> "black")

let get_bc_predicate = 
  (try Hashtbl.find bcolors "lpredicate" with Not_found -> "white")

let reset_last_colored () = 
  !last_colored#set_properties 
    [`BACKGROUND get_bc_predicate; `FOREGROUND get_fc_predicate];
  last_colored := GText.tag ()

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
            let _ = Hilight.token !tbuf_source lexbuf in
            ()
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
  "Hypothesis n"^(hypo s)^": "

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
  | _ -> true

let move_to_line line = 
  if line <= !tbuf_source#line_count && line <> 0 then begin
    let it = !tbuf_source#get_iter (`LINE line) in 
    let mark = `MARK (!tbuf_source#create_mark it) 
    and y = if !tbuf_source#line_count < 20 then 0.23 else 0.1 in
    let _ = !tv_source#scroll_to_mark ~use_align:true ~yalign:y mark in 
    print_endline ("     [...] Moving to line n "^(string_of_int line)); flush stdout
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

let insert_text (tbuf:GText.buffer) ty s = 
  let (fc, bc) = get_color ty 
  and it = tbuf#end_iter 
  and text = unicode_sym s in
  let new_tag = tbuf#create_tag [`BACKGROUND bc; `FOREGROUND fc] in
  tbuf#insert ~tags:[new_tag] ~iter:it text 

let insert_predicate (tbuf:GText.buffer) s =
  insert_text tbuf "predicate" s

let insert_string (tbuf:GText.buffer) s =
  let it = tbuf#end_iter in
  tbuf#insert ~iter:it s 

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

let rec ekteb_predicate (tbuf:GText.buffer) = function 
  | Pnamed (s, p) ->
      let fmt = Format.str_formatter in
      fprintf fmt "@[<hov 2>%a@]" print_predicate p;
      let loc = grab_infos s
      and text = flush_str_formatter () in
      let (fc, bc) = 
	if is_localised loc then 
	  get_color "lpredicate" 
	else get_color "predicate"
      and it = tbuf#end_iter in
      let text = unicode_sym text  
      and new_tag = tbuf#create_tag [`BACKGROUND bc; `FOREGROUND fc] in
      ignore(
	new_tag#connect#event ~callback:
	  (fun ~origin ev it -> 
	     if GdkEvent.get_type ev = `BUTTON_PRESS then 
	       move_to_source loc
	     else if GdkEvent.get_type ev = `MOTION_NOTIFY then begin
	       !last_colored#set_properties 
		 [`BACKGROUND get_bc_predicate; `FOREGROUND get_fc_predicate];
	       last_colored := new_tag;
	       new_tag#set_properties 
		 [`BACKGROUND bc_highlight; `FOREGROUND fc_highlight]
	     end;
	     false)
      );
      tbuf#insert ~tags:[new_tag] ~iter:it text 
  | Pand (_, _, p1, p2) ->
      ekteb_predicate tbuf p1;
      insert_string tbuf " /\\ ";
      ekteb_predicate tbuf p2;
  | Pimplies(_, p1, p2) ->
      ekteb_predicate tbuf p1;
      insert_string tbuf " => ";
      ekteb_predicate tbuf p2;
  | p -> 
      let fmt = Format.str_formatter in 
      print_predicate fmt p;
      let text = flush_str_formatter () in
      insert_predicate tbuf text

let print_oblig (tbuf:GText.buffer) (ctx,concl) =
    let ctx, concl = intros ctx concl 
    and fmt = Format.str_formatter in 
    let rec print_list sep print = function
      | [] -> ()
      | p::r ->
	  print p;
	  insert_string tbuf sep;
	  print_list sep print r 
    and print_hyp fmt = function
      | Svar (id, t) ->
	  fprintf fmt "%a: " Ident.print id;
	  insert_text tbuf "var" (flush_str_formatter ());
          fprintf fmt "@[%a@]" print_cc_type t;
	  insert_text tbuf "predicate" (flush_str_formatter ());
      | Spred (id, p) ->
	  let hypo_nb = hypo (Ident.string id) in
	  insert_text tbuf "hypothesis" (hypothesis hypo_nb);
          ekteb_predicate tbuf p;
    in
    print_list "\n" (print_hyp fmt) ctx;
    insert_text tbuf "separator" "\n_______\n\n";
    (* Conclusion *)
    ekteb_predicate tbuf concl

let is_buffer_saved = 
  Hashtbl.mem obligs

let save_buffer s (tbuf:GText.buffer) = 
  Hashtbl.add obligs s tbuf

let get_buffer = 
  Hashtbl.find obligs
  
let print_all (tbuf:GText.buffer) s p = 
  insert_text tbuf "title" (s^"\n\n");
  print_oblig tbuf p

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
