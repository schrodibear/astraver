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

open Pp
open Misc
open Util
open Vcg
open Logic
open Cc
open Format

type loc = { file:string; line:string; spos:string; fpos:string }
let fcolors = Hashtbl.create 13
let bcolors = Hashtbl.create 13
let obligs = Hashtbl.create 5501 (* Nombre premier de Sophie Germain *)
let ntags = Hashtbl.create 97
let tags = ref 0
let last_fct = ref None
let fcts = ref []

let _ = 
  Hashtbl.add fcolors "title" "brown";
  Hashtbl.add fcolors "var" "darkgreen";
  Hashtbl.add fcolors "predicate" "blue";
  Hashtbl.add fcolors "information" "orange";
  Hashtbl.add fcolors "separator" "brown";
  Hashtbl.add fcolors "hypothesis" "orange";
  Hashtbl.add fcolors "conclusion" "red"

let _ = 
  Hashtbl.add bcolors "title" "yellow"

let get_color ty = 
  (try Hashtbl.find fcolors ty with Not_found -> "black") , 
  (try Hashtbl.find bcolors ty with Not_found -> "white")

let unicode_sym s = s

let new_tag () = 
  tags := !tags + 1;
  (string_of_int !tags)

let unknown_tag () = 
  "hyp_none_"^(new_tag ())

let fct_name nb = 
  match !last_fct with
    | None -> assert false
    | Some s -> s^"_"^nb

let hypo s = (* Model : HW_11 *)
  let r = Str.regexp "\\HW_\\([0-9]+\\)" in
  if Str.string_match r s 0 then
    (Str.matched_group 1 s)
  else
    s

let hypothesis s = 
  "Hypothesis n"^(hypo s)^":"

let grab_infos hypo s = 
  let r = Str.regexp "File \"\\(.+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)" in
  if Str.string_match r s 0 then
    Hashtbl.add obligs hypo {file=(Str.matched_group 1 s);
			     line=(Str.matched_group 2 s);
			     spos=(Str.matched_group 3 s);
			     fpos=(Str.matched_group 4 s)}

(* Est ce que le nom d'une hypothese est unique ???
   - si oui, alors mettre fonction^hypo_nb comme cle dans la Hashtable
   - si non, tout est bien dans le meilleur des mondes :D 

   Inconvenient : une hypothese est rajoutee autant de fois qu'elle 
   apparait dans les obligations car on ne peut pas placer plusieurs
   tags portant le meme nom dans le meme GText.buffer , meme dans 
   differents evenements.
*)

let get_location s = 
  try 
    Some(Hashtbl.find obligs s)
  with Not_found -> None

let tag_to_name t = 
  try
    Some(Hashtbl.find ntags t)
  with Not_found -> None

let get_new_tag (tbuf:GText.buffer) (title:string) (bc:string) (fc:string) = 
  let newtag = tbuf#create_tag ~name:title [`BACKGROUND bc; `FOREGROUND fc] in
  Hashtbl.add ntags newtag title;
  newtag

let insert_text (tbuf:GText.buffer) ty ?(loc = None) s = 
  let (fc, bc) = get_color ty 
  and it = tbuf#end_iter 
  and text = unicode_sym s 
  and tag = 
    (match loc with
    | None -> unknown_tag ()
    | Some s -> s)
  in
  let new_tag = get_new_tag tbuf tag bc fc in 
  tbuf#insert ~tags:[new_tag] ~iter:it text 

let insert_predicate (tbuf:GText.buffer) ?(loc = None) s =
  let ty = "predicate" in
  match loc with
    | None -> insert_text tbuf ty s
    | Some nb -> 
	let mytag = fct_name nb in
	if not (Hashtbl.mem obligs mytag) then (
	  insert_text tbuf ty ~loc:(Some(mytag)) s;
	  grab_infos mytag s
	) else (
	  let t = mytag^"_"^(new_tag ()) in 
	  insert_text tbuf ty ~loc:(Some(t)) s;
	  grab_infos t s
	)
	

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

let rec print_predicate fmt = function 
  | Pnamed (_, p) -> 
      Format.fprintf fmt "@[<hov 2>%a@]" print_predicate p
  | p -> 
      Coq.print_predicate_v8 fmt p

let print_cc_type = Coq.print_cc_type_v8

let print_oblig (tbuf:GText.buffer) (ctx,concl) =
    let ctx, concl = intros ctx concl 
    and fmt = Format.str_formatter in 
    let print_hyp fmt = function
      | Svar (id, t) ->
	  fprintf fmt "%a: " Ident.print id;
	  insert_text tbuf "var" (flush_str_formatter ());
          fprintf fmt "@[%a@]" print_cc_type t;
	  insert_text tbuf "predicate" (flush_str_formatter ());
      | Spred (id, p) ->
	  let hypo_nb = hypo (Ident.string id) in
	  insert_text tbuf "hypothesis" ("\n"^(hypothesis hypo_nb));
          fprintf fmt "@[<hov 2>%a@]" print_predicate p;
	  insert_predicate tbuf ~loc:(Some(hypo_nb)) (flush_str_formatter ());
    in
    fprintf fmt "@[@\n%a@]" (print_list newline print_hyp) ctx;
    insert_text tbuf "predicate" (flush_str_formatter ());

    insert_text tbuf "separator" "\n_______\n\n";

    print_predicate fmt concl;
    insert_text tbuf "conclusion" (flush_str_formatter ())

let text_of_obligation (tbuf:GText.buffer) (o,s,p) =
  Hashtbl.clear obligs;
  insert_text tbuf "title" (s^"\n");
  last_fct := Some(s);
  (if not (List.mem s !fcts) then fcts := s :: !fcts);
  print_oblig tbuf p
