(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
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

let push_decl d = 
  Encoding.push ~encode_preds:false ~encode_funs:false
    ~encode_inductive:false ~encode_algtype:false d

let iter = Encoding.iter


(*
  let capitalize s =
  let is_alpha n = ('a' <= n && n <= 'z') || ('A' <= n && n <= 'Z') in
  let s = if not (is_alpha s.[0]) then "Un"^s else s in
  String.capitalize s
*)

let ident fmt s = 
  let s = Ident.string s in
  let s = 
    if 'A' <= s.[0] && s.[0] <= 'Z' then "_" ^ s  else s
  in
  pp_print_string fmt s

let string_capitalize fmt s =
  let s = 
    if s.[0] = '_' then "U"^s else 
    if 'a' <= s.[0] && s.[0] <= 'z' 
    then String.capitalize s
    else s
  in
  pp_print_string fmt s

let ident_capitalize fmt s = 
  string_capitalize fmt (Ident.string s)

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

let t_single = Ident.create "single"
let t_double = Ident.create "double"
let t_mode = Ident.create "mode"

let print_builtin_type fmt = function
  | id when id == t_single -> Pp.string fmt "Single.single"
  | id when id == t_double -> Pp.string fmt "Double.double"
  | id when id == t_mode -> Pp.string fmt "Rounding.mode"
  | id -> ident fmt id

let rec pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "Bool.bool"
  | PTunit -> fprintf fmt "()"
  | PTreal -> fprintf fmt "real"
  | PTexternal ([],id) -> print_builtin_type fmt id
  | PTvar {tag=t; type_val=None} -> type_var fmt t
  | PTvar {tag=_t; type_val=Some pt} -> pure_type fmt pt
  | PTexternal (l,id) -> fprintf fmt "(%a %a)"
      ident id (print_list space pure_type) l



let t_computer_div = Ident.create "computer_div"
let t_computer_mod = Ident.create "computer_mod"

let builtins_table =  
    [
      t_add_int , "Int.(+)";
      t_sub_int , "Int.(-)";
      t_mul_int , "Int.(*)";
      t_computer_div , "ComputerDivision.div";
      t_computer_mod , "ComputerDivision.mod";
      t_neg_int , "Int.(-_)";
      t_add_real , "Real.(+)";
      t_sub_real , "Real.(-)";
      t_mul_real , "Real.(*)";
      t_div_real , "Real.(/)";
      t_neg_real , "Real.(-_)";
      t_lt_int , "Int.(<)" ;
      t_le_int , "Int.(<=)";
      t_gt_int , "Int.(>)";
      t_ge_int , "Int.(>=)";
      t_lt_real , "Real.(<)" ;
      t_le_real , "Real.(<=)";
      t_gt_real , "Real.(>)";
      t_abs_real , "AbsReal.abs";
      t_abs_int , "AbsInt.abs";

      Ident.create "nearest_even", "Rounding.NearestTiesToEven" ;
      Ident.create "to_zero", "Rounding.ToZero" ;
      Ident.create "up", "Rounding.Up" ;
      Ident.create "down", "Rounding.Down" ;
      Ident.create "nearest_away", "Rounding.NearTiesToAway" ;

      Ident.create "round_single", "Single.round" ;
      Ident.create "round_double", "Double.round" ;
      Ident.create "single_value", "Single.value";
      Ident.create "double_value", "Double.value";
    ]

let constructor_table = Hashtbl.create 17

let print_builtin fmt id = 
  try
    let s = List.assq id builtins_table in
    Pp.string fmt s
  with Not_found -> 
    if Hashtbl.mem constructor_table id
    then
      ident_capitalize fmt id
    else ident fmt id

let rec term fmt = function
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool b) -> 
      if b 
      then fprintf fmt "Bool.True"
      else fprintf fmt "Bool.False"
  | Tconst ConstUnit -> 
      fprintf fmt "()"
  | Tconst (ConstFloat c) ->
      Print_real.print fmt c
  | Tvar id | Tderef id -> ident fmt id
  | Tapp (id, tl, instance) -> 
      let ret_type =
        let var_subst,logic = Env.find_global_logic id in
        Env.instantiate_specialized var_subst instance;
        match logic with
          | Predicate _ -> assert false
          | Function (_,ret_type) -> ret_type in
      begin match tl with
(*
        | [] -> fprintf fmt "(%a : %a)" ident id pure_type ret_type
*)
        | _ ->
            fprintf fmt "(%a %a : %a)"
              print_builtin id (print_list space term) tl
              pure_type ret_type
      end      
  | Tnamed (User n, t) ->
      fprintf fmt "@[(%S@ %a)@]" n term t
  | Tnamed (_, t) -> term fmt t

let rec predicate fmt = function
  | Pvar id | Papp (id, [], _) -> 
      ident fmt id
  | Papp (id, [t1; t2], _) when is_eq id ->
      fprintf fmt "(%a = %a)" term t1 term t2
  | Papp (id, [t1; t2], _) when is_neq id ->
      fprintf fmt "(%a <> %a)" term t1 term t2
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[((Int.(<=) 0 %a) and@ (Int.(<) %a %a))@]"
        term b term a term b
  | Papp (id, [_t], _) when id == well_founded ->
      fprintf fmt "@[false (* was well_founded(...) *)@]" 
  | Papp (id, l, _) ->
      fprintf fmt "(%a %a)" print_builtin id (print_list space term) l
  | Ptrue ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pimplies (_, a, b) -> 
      fprintf fmt "(@[%a ->@ %a@])" predicate a predicate b
  | Piff (a, b) -> 
      fprintf fmt "(@[%a <->@ %a@])" predicate a predicate b
  | Pif (a, b, c) -> 
      fprintf fmt "(@[if %a = Bool.True then@ %a else@ %a@])" 
	term a predicate b predicate c
  | Pand (_, _, a, b) ->
      fprintf fmt "(@[%a and@ %a@])" predicate a predicate b
  | Forallb (_, _ptrue, _pfalse) -> assert false (* TODO What is it? *)
      (* fprintf fmt "(@[forallb(%a,@ %a)@])"  *)
      (*   predicate ptrue predicate pfalse *)
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
      fprintf fmt "@[(%S@ %a)@]" n predicate p
  | Pnamed (_, p) -> predicate fmt p

and print_pattern fmt = function
  | TPat t -> term fmt t
  | PPat p -> predicate fmt p

and print_triggers fmt = function
  | [] -> 
      ()
  | tl -> 
      fprintf fmt " [%a]" (print_list alt (print_list comma print_pattern)) tl

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
  fprintf fmt "(%a : %a)" ident id pure_type pt

let logic_type fmt = function
  | Predicate [] -> ()
  | Function ([], pt) -> fprintf fmt " : %a" pure_type pt
  | Predicate ptl -> fprintf fmt "%a" (print_list space pure_type) ptl
  | Function (ptl, pt) -> 
      fprintf fmt "%a : %a" (print_list space pure_type) ptl pure_type pt

let type_parameters fmt l = 
  let type_var fmt id = fprintf fmt "'%s" id in
  match l with
  | [] -> ()
  | l -> fprintf fmt " %a" (print_list space type_var) l

let alg_type_parameters fmt = function
  | [] -> ()
  | l -> fprintf fmt "%a " (print_list space pure_type) l

let alg_type_constructor fmt (c,pl) =
  Hashtbl.add constructor_table c ();
  match pl with
  | [] -> fprintf fmt "| %a" ident_capitalize c
  | _  -> fprintf fmt "| %a (@[%a@])" ident_capitalize c
            (print_list space (* or comma ? *) pure_type) pl

let alg_type_single fmt (_, id, d) =
  let vs,cs = specialize d in
  fprintf fmt "@[%a %a@] =@\n  @[%a@]"
    ident id alg_type_parameters vs
    (print_list newline alg_type_constructor) cs

let decl fmt d = 
  match d with
  | Dtype (_, id, pl) ->
      fprintf fmt "@[type %a%a@]" ident id type_parameters pl 
  | Dalgtype ls ->
      let andsep fmt () = fprintf fmt "@\n" in
      fprintf fmt "@[type %a@]" (print_list andsep alg_type_single) ls
  | Dlogic (_, id, lt) ->
      let lt = specialize lt in
      fprintf fmt "@[logic %a %a@]" ident id logic_type lt
  | Dpredicate_def (_, id, def) ->
      let bl,p = specialize def in
      fprintf fmt "@[<hov 2>logic %a %a =@ %a@]" ident id 
	(print_list space logic_binder) bl predicate p
  | Dinductive_def (_, id, indcases) ->
      let bl,l = specialize indcases in
      begin match l with
        | [] ->       fprintf fmt 
	    "@[<hov 0>inductive %a %a@]" 
	      ident id 
	      (print_list space pure_type) bl 
        | _ ->
            fprintf fmt 
	      "@[<hov 0>inductive %a %a@] =@\n  @[<v 0>%a@]@\n@\n@]" 
	      ident id 
	      (print_list space pure_type) bl 
	      (print_list newline 
	         (fun fmt (id,p) -> fprintf fmt "@[| %a: %a@]" 
                    ident_capitalize id predicate p)) l
      end
  | Dfunction_def (_, id, def) ->
      let bl,pt,t = specialize def in
      fprintf fmt "@[<hov 2>logic %a %a : %a =@ %a@]" ident id
	(print_list space logic_binder) bl pure_type pt term t
  | Daxiom (_, id, p) ->
      let p = specialize p in
      fprintf fmt "@[<hov 2>axiom %a:@ %a@]" 
        string_capitalize id predicate p
  | Dgoal (_, _expl, id, sq) ->
      let sq = specialize sq in
      fprintf fmt "@[<hov 2>goal %s:@\n%a@]" 
        (String.capitalize id) sequent sq

let decl fmt d = fprintf fmt "@[%a@]@\n@\n" decl d

(*
let print_file fmt = 
  fprintf fmt "@[<hov 2>theory Why2@\n";
  fprintf fmt "use Tuple0@\n";
  fprintf fmt "use int.Int@\n";
  fprintf fmt "use int.Abs as AbsInt@\n";
  fprintf fmt "use int.ComputerDivision@\n";
  fprintf fmt "use real.Real@\n";
  fprintf fmt "use real.Abs as AbsReal@\n";
  fprintf fmt "use bool.Bool@\n";
  iter (decl fmt);
  fprintf fmt "@]@\nend@?"

let print_trace fmt id expl =
  fprintf fmt "[%s]@\n" id;
  Explain.print fmt expl;
  fprintf fmt "@\n"

let print_traces fmt =
  iter
    (function
       | Dgoal (_loc, expl, id, _) -> print_trace fmt id ((*loc,*)expl)
       | _ -> ())

let output_file f =
  print_in_file print_file (Options.out_file (f ^ "_why3.why"))
*)

(*

let output_files f =
  eprintf "Starting Multi-Why output with basename %s@." f;
  let po = ref 0 in
  print_in_file
    (fun ctxfmt ->
       iter 
	 (function 
	    | Dgoal (_loc,expl,id,_) as d -> 
		incr po;		
		let fpo = f ^ "_po" ^ string_of_int !po ^ ".why" in
		print_in_file (fun fmt -> decl fmt d) fpo;
		if explain_vc then
		  let ftr = f ^ "_po" ^ string_of_int !po ^ ".xpl" in
		  print_in_file (fun fmt -> print_trace fmt id ((*loc,*)expl)) 
                    ftr
	    | d -> 
		decl ctxfmt d))
    (f ^ "_ctx.why");
  eprintf "Multi-Why output done@."
  
let push_or_output_decl = 
  let po = ref 0 in 
  function d ->
    match d with
      | Dgoal (_loc,expl,id,_) as d -> 
	  incr po;
	  let fpo = Options.out_file (id ^ ".why") in
	  print_in_file (fun fmt -> decl fmt d) fpo;
	  if explain_vc then
	    let ftr = Options.out_file (id ^ ".xpl") in
	    print_in_file (fun fmt -> print_trace fmt id ((*loc,*)expl)) ftr
      | d -> push_decl d

*)

module SMap = Map.Make(String)

let escape s =
  let s = String.copy s in
  for i = 0 to String.length s - 1 do
    match s.[i] with
      | ' ' | '\'' | '`' -> s.[i] <- '_'
      | _ -> ()
  done;
  s

let print_structured_file f fmt =
  fprintf fmt "@[<hov 2>theory %s_ctx@\n" f;
  fprintf fmt "use int.Int@\n";
  fprintf fmt "use int.Abs as AbsInt@\n";
  fprintf fmt "use int.ComputerDivision@\n";
  fprintf fmt "use real.Real@\n";
  fprintf fmt "use real.Abs as AbsReal@\n";
  fprintf fmt "use bool.Bool@\n";
  fprintf fmt "use floating_point.Rounding@\n";
  fprintf fmt "use floating_point.Single@\n";
  fprintf fmt "use floating_point.Double@\n";
  let lemmas = ref [] in
  let functions = ref SMap.empty in
  iter 
    (function 
       | Dgoal (_,e,_id,_) as d -> 
	   begin
	     match e.vc_kind with
	       | EKLemma -> 
		   lemmas := d :: !lemmas;
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
		     SMap.add e.behavior (d::vcs) behs
		   in
		   functions := SMap.add fn behs !functions;
	   end
       | d -> 
	   decl fmt d);
  (* add any function which have no VC *)
  Hashtbl.iter 
    (fun _key (fn,_beh,_loc) -> 
       try
	 let _ = SMap.find fn !functions in ()
       with Not_found ->
	 functions := SMap.add fn SMap.empty !functions)  
    Util.program_locs ;
  (* outputs the lemmas and close the ctx theory*)
  List.iter (decl fmt) (List.rev !lemmas);
  fprintf fmt "@]@\nend@\n@.";
  (* outputs the VCs *)
  SMap.iter
    (fun fname behs ->
(*
       let floc =
	 try 
	   let (_,_,floc) = Hashtbl.find Util.program_locs fname in
	   floc
	 with Not_found -> Loc.dummy_floc
       in
*)
       SMap.iter
	 (fun beh vcs ->
	    fprintf fmt "@[<hov 2>theory %s_%s@\n" (escape fname) (escape beh);
	    fprintf fmt "use import %s_ctx@\n" f;
	    List.iter (decl fmt) (List.rev vcs);
	    fprintf fmt "@]@\nend@\n@.")
	 behs)
    !functions

let output_structured_file f =
  print_in_file 
    (print_structured_file (String.capitalize (Filename.basename f))) 
    (Options.out_file (f ^ "_why3.why"))

let output_file = output_structured_file
