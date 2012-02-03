(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



open Format
open Pp
open Ident
open Options
open Misc
open Logic
open Logic_decl

let reset = Encoding.reset

let ergo = ref false

let push_decl ?(ergo=false) d =
  if ergo
  then Encoding.push ~encode_preds:false ~encode_funs:false d
  else Encoding.push ~encode_preds:false ~encode_funs:false
    ~encode_inductive:false ~encode_algtype:false d

let iter = Encoding.iter

let ident fmt id =
  let s = Ident.string id in
  let s = if s = "farray" then "why__farray" else s in (* Alt-ergo keyword *)
  pp_print_string fmt s

let type_vars = Hashtbl.create 17

let type_var fmt n =
  try
    fprintf fmt "'a%d" (Hashtbl.find type_vars n)
  with Not_found ->
    assert false

let specialize s =
  Hashtbl.clear type_vars;
  let n = ref 0 in
  Env.Vset.iter
    (fun tv -> incr n; Hashtbl.add type_vars tv.tag !n) s.Env.scheme_vars;
  s.Env.scheme_type

let rec pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTreal -> fprintf fmt "real"
  | PTexternal ([],id) -> fprintf fmt "%a" ident id
  | PTvar {tag=t; type_val=None} -> type_var fmt t
  | PTvar {tag=_t; type_val=Some pt} -> pure_type fmt pt
  | PTexternal ([t],id) ->
      fprintf fmt "%a %a" pure_type t ident id
  | PTexternal (l,id) -> fprintf fmt "(%a) %a"
      (print_list comma pure_type) l ident id

let rec term fmt = function
  | Tconst (ConstInt n) ->
      fprintf fmt "%s" n
  | Tconst (ConstBool b) ->
      fprintf fmt "%b" b
  | Tconst ConstUnit ->
      fprintf fmt "void"
  | Tconst (ConstFloat c) ->
      Print_real.print fmt c
  | Tvar id | Tderef id | Tapp (id, [], _) ->
      ident fmt id
  | Tapp (id, [t1; t2], _) when id == t_add_int || id == t_add_real ->
      fprintf fmt "(%a + %a)" term t1 term t2
  | Tapp (id, [t1; t2], _) when id == t_sub_int || id == t_sub_real ->
      fprintf fmt "(%a - %a)" term t1 term t2
  | Tapp (id, [t1; t2], _) when id == t_mul_int || id == t_mul_real ->
      fprintf fmt "(%a * %a)" term t1 term t2
(*
  | Tapp (id, [t1; t2], _) when id == t_div_int ->
      if !ergo then
        fprintf fmt "computer_div(%a,%a)" term t1 term t2
      else
        fprintf fmt "(%a / %a)" term t1 term t2
*)
(*
  | Tapp (id, [t1; t2], _) when id == t_mod_int ->
      if !ergo then
        fprintf fmt "computer_mod(%a,%a)" term t1 term t2
      else
        fprintf fmt "(%a %% %a)" term t1 term t2
*)
  | Tapp (id, [t1], _) when id == t_neg_int || id == t_neg_real ->
      fprintf fmt "(-%a)" term t1
  | Tapp (id, tl, _) ->
      fprintf fmt "%a(%a)" ident id (print_list comma term) tl
  | Tnamed (User n, t) ->
      fprintf fmt "@[(%S:@ %a)@]" n term t
  | Tnamed (_, t) -> term fmt t

let int_relation_string id =
  if id == t_lt_int then "<"
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  else assert false

let real_relation_string id =
  if id == t_lt_real then "<"
  else if id == t_le_real then "<="
  else if id == t_gt_real then ">"
  else if id == t_ge_real then ">="
  else assert false

let rec predicate fmt = function
  | Pvar id | Papp (id, [], _) ->
      ident fmt id
  | Papp (id, [t1; t2], _) when is_eq id ->
      fprintf fmt "(%a = %a)" term t1 term t2
  | Papp (id, [t1; t2], _) when is_neq id ->
      fprintf fmt "(%a <> %a)" term t1 term t2
  | Papp (id, [t1; t2], _) when is_int_comparison id ->
      fprintf fmt "(%a %s %a)" term t1 (int_relation_string id) term t2
  | Papp (id, [t1; t2], _) when is_real_comparison id ->
      fprintf fmt "(%a %s %a)" term t1 (real_relation_string id) term t2
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[((0 <= %a) and@ (%a < %a))@]" term b term a term b
  | Papp (id, [_t], _) when id == well_founded ->
      fprintf fmt "@[false (* was well_founded(...) *)@]"
  | Papp (id, l, _) ->
      fprintf fmt "%s(%a)" (Ident.string id) (print_list comma term) l
  | Ptrue ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pimplies (_, a, b) ->
      fprintf fmt "(@[%a ->@ %a@])" predicate a predicate b
  | Piff (a, b) ->
      fprintf fmt "(@[%a <->@ %a@])" predicate a predicate b
  | Pif (a, b, c) ->
      fprintf fmt "(@[if %a then@ %a else@ %a@])"
	term a predicate b predicate c
  | Pand (_, _, a, b) ->
      fprintf fmt "(@[%a and@ %a@])" predicate a predicate b
  | Forallb (_, ptrue, pfalse) ->
      fprintf fmt "(@[forallb(%a,@ %a)@])"
	predicate ptrue predicate pfalse
  | Por (a, b) ->
      fprintf fmt "(@[%a or@ %a@])" predicate a predicate b
  | Pnot a ->
      fprintf fmt "(not %a)" predicate a
  | Forall (_,id,n,v,tl,p) ->
      let id = next_away id (predicate_vars p) in
      let s = subst_onev n id in
      let p = subst_in_predicate s p in
      let tl = List.map (List.map (subst_in_pattern s)) tl in
      fprintf fmt "@[<hov 2>(forall %a:%a%a.@ %a)@]"
	ident id pure_type v print_triggers tl predicate p
  | Exists (id,n,v,p) ->
      let id = next_away id (predicate_vars p) in
      let p = subst_in_predicate (subst_onev n id) p in
      fprintf fmt "@[<hov 2>(exists %a:%a.@ %a)@]"
	ident id pure_type v predicate p
  | Plet (id, n, _, t, p) ->
      if false then  (* TODO: alt-ergo has no let support yet. *)
        let id = next_away id (predicate_vars p) in
        let p = subst_in_predicate (subst_onev n id) p in
        fprintf fmt "@[<hov 2>(let %a = %a in@ %a)@]"
	  ident id term t predicate p
      else
        let p = tsubst_in_predicate (subst_one n t) p in
        fprintf fmt "@[%a@]" predicate p
  | Pnamed (User n, p) ->
      fprintf fmt "@[(%S:@ %a)@]" n predicate p
  | Pnamed (_, p) -> predicate fmt p

and print_pattern fmt = function
  | TPat t -> term fmt t
  | PPat p -> predicate fmt p

and print_triggers fmt l =
  let l =
    if !ergo then
      List.rev
        (List.fold_left 
           (fun acc pl ->
             let pl = List.fold_left 
               (fun acc p ->
                 match p with
                   | PPat(Papp (id, _, _)) when is_eq id -> acc
                   | _ -> p::acc)
               [] pl
             in
             match pl with [] -> acc | _ -> (List.rev pl)::acc)
           [] l)
    else l
  in
  match l with
  | [] -> ()
  | _ ->
      fprintf fmt " [%a]" (print_list alt (print_list comma print_pattern)) l

let sequent fmt (ctx, p) =
  let context fmt = function
    | Cc.Svar (id, pt) ->
	fprintf fmt "forall %a:%a." ident id pure_type pt
    | Cc.Spred (_, p) ->
	fprintf fmt "@[%a ->@]" predicate p
  in
  print_list newline context fmt ctx;
  if ctx <> [] then fprintf fmt "@\n";
  predicate fmt p

let logic_binder fmt (id, pt) =
  fprintf fmt "%a: %a" ident id pure_type pt

let logic_type fmt = function
  | Predicate [] ->
      fprintf fmt "prop"
  | Function ([], pt) ->
      fprintf fmt "%a" pure_type pt
  | Predicate ptl ->
      fprintf fmt "%a -> prop" (print_list comma pure_type) ptl
  | Function (ptl, pt) ->
      fprintf fmt "%a -> %a" (print_list comma pure_type) ptl pure_type pt

let type_parameters fmt l =
  let type_var fmt id = fprintf fmt "'%s" id in
  match l with
  | [] -> ()
  | [id] -> fprintf fmt "%a " type_var id
  | l -> fprintf fmt "(%a) " (print_list comma type_var) l

let alg_type_parameters fmt = function
  | [] -> ()
  | [id] -> fprintf fmt "%a " pure_type id
  | l -> fprintf fmt "(%a) " (print_list comma pure_type) l

let alg_type_constructor fmt (c,pl) =
  match pl with
  | [] -> fprintf fmt "| %a" ident c
  | _  -> fprintf fmt "| %a (@[%a@])" ident c
            (print_list comma pure_type) pl

let alg_type_single fmt (_, id, d) =
  let vs,cs = specialize d in
  fprintf fmt "@[%a%a@] =@\n  @[%a@]"
    alg_type_parameters vs ident id
    (print_list newline alg_type_constructor) cs

let decl fmt d =
  match d with
  | Dtype (_, id, pl) ->
      fprintf fmt "@[type %a%a@]" type_parameters pl ident id
  | Dalgtype ls ->
      let andsep fmt () = fprintf fmt "@\n and " in
      fprintf fmt "@[type %a@]" (print_list andsep alg_type_single) ls
  | Dlogic (_, id, lt) ->
      let lt = specialize lt in
      fprintf fmt "@[logic %a : %a@]" ident id logic_type lt
  | Dpredicate_def (_, id, def) ->
      let bl,p = specialize def in
      fprintf fmt "@[<hov 2>predicate %a(%a) =@ %a@]" ident id
	(print_list comma logic_binder) bl predicate p
  | Dinductive_def (_, id, indcases) ->
      let bl,l = specialize indcases in
      fprintf fmt
	"@[<hov 0>inductive %a: @[%a -> prop@] =@\n  @[<v 0>%a@]@\n@\n@]"
	ident id
	(print_list comma pure_type) bl
	(print_list newline
	   (fun fmt (id,p) -> fprintf fmt "@[| %a: %a@]" ident id predicate p)) l
  | Dfunction_def (_, id, def) ->
      let bl,pt,t = specialize def in
      fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]" ident id
	(print_list comma logic_binder) bl pure_type pt term t
  | Daxiom (_, id, p) ->
      let p = specialize p in
      fprintf fmt "@[<hov 2>axiom %s:@ %a@]" id predicate p
  | Dgoal (_, is_lemma, _, id, sq) ->
      let sq = specialize sq in
      if !ergo then
	begin
	  fprintf fmt "@[<hov 2>goal %s:@\n%a@]" id sequent sq;
	  if is_lemma then
	    fprintf fmt "@\n@\n@[<hov 2>axiom %s_as_axiom:@\n%a@]" id sequent sq
	end
      else
	fprintf fmt "@[<hov 2>%s %s:@\n%a@]"
	  (if is_lemma then "lemma" else "goal")
	  id sequent sq

let decl fmt d = fprintf fmt "@[%a@]@\n@\n" decl d

let print_file ~ergo:b fmt =
  ergo := b;
  iter (decl fmt);
  ergo := false

let print_trace fmt id expl =
  fprintf fmt "[%s]@\n" id;
  Explain.print fmt expl;
  fprintf fmt "@\n"

let print_traces fmt =
  iter
    (function
       | Dgoal (_loc, _, expl, id, _) -> print_trace fmt id ((*loc,*)expl)
       | _ -> ())

let output_file ~ergo f =
  print_in_file (print_file ~ergo) (Options.out_file f)
(* cannot work as is, pb with temp files
  if explain_vc && not ergo then
    print_in_file print_traces (Options.out_file (f ^ ".xpl"))
*)

let output_files f =
  eprintf "Starting Multi-Why output with basename %s@." f;
  let po = ref 0 in
  print_in_file
    (fun ctxfmt ->
       iter
	 (function
	    | Dgoal (_loc,_,expl,id,_) as d ->
		incr po;
		let fpo = f ^ "_po" ^ string_of_int !po ^ ".why" in
		print_in_file (fun fmt -> decl fmt d) fpo;
		if explain_vc then
		  let ftr = f ^ "_po" ^ string_of_int !po ^ ".xpl" in
		  print_in_file (fun fmt -> print_trace fmt id ((*loc,*)expl)) ftr
	    | d ->
		decl ctxfmt d))
    (f ^ "_ctx.why");
  eprintf "Multi-Why output done@."

let push_or_output_decl =
  let po = ref 0 in
  function d ->
    match d with
      | Dgoal (_loc,_is_lemma,expl,id,_) as d ->
	  incr po;
	  let fpo = Options.out_file (id ^ ".why") in
	  print_in_file (fun fmt -> decl fmt d) fpo;
	  if explain_vc then
	    let ftr = Options.out_file (id ^ ".xpl") in
	    print_in_file (fun fmt -> print_trace fmt id ((*loc,*)expl)) ftr
      | d -> push_decl d

module SMap = Map.Make(String)

let output_project f =
  let po = ref 0 in
  let lemmas = ref [] in
  let functions = ref SMap.empty in
  print_in_file
    (fun ctxfmt ->
       iter
	 (function
	    | Dgoal (_,_is_lemma,e,_id,_) as d ->
		incr po;
		let fpo = f ^ "_po" ^ string_of_int !po ^ ".why" in
		print_in_file (fun fmt -> decl fmt d) fpo;
		begin
		  match e.vc_kind with
		    | EKLemma ->
			lemmas := (e,fpo) :: !lemmas;
		    | _ ->
			let fn = e.lemma_or_fun_name in
			let behs =
			  try SMap.find fn !functions
			  with Not_found -> SMap.empty
			in
			let vcs =
			  try SMap.find e.behavior behs
			  with Not_found -> []
			in
			let behs =
			  SMap.add e.behavior ((e,fpo)::vcs) behs
			in
			functions := SMap.add fn behs !functions;
		end
	    | d ->
		decl ctxfmt d))
    (f ^ "_ctx.why");
  Hashtbl.iter
    (fun _key (fn,_beh,_loc) ->
       try
	 let _ = SMap.find fn !functions in ()
       with Not_found ->
	 functions := SMap.add fn SMap.empty !functions)
    Util.program_locs ;
  let p = Project.create (Filename.basename f) in
  Project.set_project_context_file p (f ^ "_ctx.why");
  List.iter
    (fun (expl,fpo) ->
       let n = expl.lemma_or_fun_name in
       let _ = Project.add_lemma p n expl fpo in ())
    !lemmas;
  SMap.iter
    (fun fname behs ->
       let floc =
	 try
	   let (_,_,floc) = Hashtbl.find Util.program_locs fname in
	   floc
	 with Not_found -> Loc.dummy_floc
       in
       let f = Project.add_function p fname floc in
       SMap.iter
	 (fun beh vcs ->
	    let be = Project.add_behavior f beh floc in
	    List.iter
	      (fun (expl,fpo) ->
		 let _ = Project.add_goal be expl fpo in ())
	      vcs)
	 behs)
    !functions;
  Project.save p f;
  p
