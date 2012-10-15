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
open Jc_env
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Jc_output_misc
open Pp


let is_not_true (p : Jc_ast.pexpr) =
  match p#node with
    | JCPEconst (JCCboolean true) -> false
    | _ -> true

let bin_op = function
  | `Blt -> "<"
  | `Bgt -> ">"
  | `Ble -> "<="
  | `Bge -> ">="
  | `Beq -> "=="
  | `Bneq -> "!="
  | `Badd -> "+"
  | `Bsub -> "-"
  | `Bmul -> "*"
  | `Bdiv -> "/"
  | `Bmod -> "%"
  | `Bland -> "&&"
  | `Blor -> "||"
  | `Bimplies -> "==>"
  | `Biff -> "<==>"
  | `Bbw_and -> "&"
  | `Bbw_or -> "|"
  | `Bbw_xor -> "^"
  | `Blogical_shift_right -> ">>"
  | `Barith_shift_right -> ">>>"
  | `Bshift_left -> "<<"
  | `Bconcat -> "@"

let unary_op = function
  | `Uplus -> "+"
  | `Uminus -> "-"
  | `Unot -> "!"
  | `Upostfix_inc | `Uprefix_inc -> "++"
  | `Upostfix_dec | `Uprefix_dec -> "--"
  | `Ubw_not -> "~"

let rec ppattern fmt p =
  match p#node with
    | JCPPstruct(st, lbls) ->
	fprintf fmt "@[<hv 2>%s{@ " st#name;
	List.iter
	  (fun (lbl, pat) ->
	     fprintf fmt "%s = %a;@ " lbl#name ppattern pat)
          lbls;
	fprintf fmt "}@]"
    | JCPPvar vi ->
	fprintf fmt "%s" vi#name
    | JCPPor(p1, p2) ->
	fprintf fmt "(%a)@ | (%a)" ppattern p1 ppattern p2
    | JCPPas(pat, vi) ->
	fprintf fmt "(%a as %s)" ppattern pat vi#name
    | JCPPany ->
	fprintf fmt "_"
    | JCPPconst c ->
	fprintf fmt "%a" const c

let quantifier fmt = function
  | Forall -> fprintf fmt "forall"
  | Exists -> fprintf fmt "exists"

let identifier fmt id =
  fprintf fmt "%s" id#name

let rec pexpr fmt e =
  match e#node with
    | JCPElabel(lab,e) ->
	assert (lab <> "");
	fprintf fmt "@[(%s : %a)@]" lab pexpr e
    | JCPEconst c -> const fmt c
    | JCPEvar vi ->
	fprintf fmt "%s" vi
    | JCPEbinary (e1, op, e2) ->
	fprintf fmt "@[<hv 2>(%a %s@ %a)@]" pexpr e1 (bin_op op) pexpr e2
    | JCPEunary((`Upostfix_dec | `Upostfix_inc) as op,e1) ->
	fprintf fmt "@[(%a %s)@]" pexpr e1 (unary_op op)
    | JCPEunary(op,e1) ->
	fprintf fmt "@[(%s %a)@]" (unary_op op) pexpr e1
    | JCPEif (e1,e2,e3) ->
	fprintf fmt "@[(if %a then %a else %a)@]" pexpr e1 pexpr e2 pexpr e3
    | JCPElet(Some ty,vi,Some e1,e2) ->
	fprintf fmt "@[(let %a %s =@ %a@ in %a)@]"
          ptype ty vi pexpr e1 pexpr e2
    | JCPElet(None,vi,Some e1,e2) ->
	fprintf fmt "@[(let %s =@ %a@ in %a)@]"
          vi pexpr e1 pexpr e2
    | JCPElet(_ty,_vi,None,_e2) -> assert false
    | JCPEassign (v, e) ->
	fprintf fmt "(%a = %a)" pexpr v pexpr e
    | JCPEassign_op (v, op, e) ->
	fprintf fmt "%a %s= %a" pexpr v (bin_op op) pexpr e
    | JCPEcast (e, si) ->
	fprintf fmt "(%a :> %a)" pexpr e ptype si
    | JCPEalloc (e, si) ->
	fprintf fmt "(new %s[%a])" si pexpr e
    | JCPEfree (e) ->
	fprintf fmt "(free(%a))" pexpr e
    | JCPEoffset(k,e) ->
	fprintf fmt "\\offset_m%a(%a)" offset_kind k pexpr e
    | JCPEaddress(absolute,e) ->
	fprintf fmt "\\%aaddress(%a)" address_kind absolute pexpr e
    | JCPEbase_block(e) ->
	fprintf fmt "\\base_block(%a)" pexpr e
    | JCPEfresh(e) ->
	fprintf fmt "\\fresh(%a)" pexpr e
    | JCPEinstanceof (e, si) ->
	fprintf fmt "(%a <: %s)" pexpr e si
    | JCPEderef (e, fi) ->
	fprintf fmt "%a.%s" pexpr e fi
    | JCPEmatch (e, pel) ->
	fprintf fmt "@[<v 2>match %a with@ " pexpr e;
	List.iter
	  (fun (p, e) -> fprintf fmt "  @[<v 2>%a ->@ %a;@]@ "
	     ppattern p pexpr e) pel;
	fprintf fmt "end@]"
    | JCPEold t -> fprintf fmt "@[\\old(%a)@]" pexpr t
    | JCPEat(t,lab) -> fprintf fmt "@[\\at(%a,%a)@]" pexpr t label lab
    | JCPEapp(f,labs,args) ->
	fprintf fmt "%s%a(@[%a@])" f
	  (fun fmt labs -> if List.length labs = 0 then () else
	    fprintf fmt "%a" (print_list_delim lbrace rbrace comma label) labs) labs
	  (print_list comma pexpr) args
    | JCPErange(t1,t2) ->
	fprintf fmt "@[[%a..%a]@]" (print_option pexpr) t1 (print_option pexpr) t2
    | JCPEquantifier (q,ty,vil,trigs, a)->
	fprintf fmt "@[<hv 2>(\\%a %a %a%a;@\n%a)@]"
	  quantifier q
	  ptype ty
	  (print_list comma identifier) vil
	  triggers trigs pexpr a
    | JCPEmutable _ ->
        fprintf fmt "\\mutable(TODO)"
    | JCPEeqtype(tag1,tag2) ->
	fprintf fmt "\\typeeq(%a,%a)" ptag tag1 ptag tag2
    | JCPEsubtype(tag1,tag2) ->
	fprintf fmt "(%a <: %a)" ptag tag1 ptag tag2
    | JCPEreturn (e) ->
	fprintf fmt "@\n(return %a)" pexpr e
    | JCPEunpack _ ->
        fprintf fmt "unpack(TODO)"
    | JCPEpack _ ->
        fprintf fmt "pack(TODO)"
    | JCPEthrow (ei, eo) ->
	fprintf fmt "@\n(throw %s %a)"
	  ei#name
	  pexpr eo
    | JCPEtry (s, hl, fs) ->
	fprintf fmt
	  "@\n@[<v 2>try %a@]%a@\n@[<v 2>finally%a@ end@]"
	  pexpr s
	  (print_list nothing handler) hl
	  pexpr fs
    | JCPEgoto lab ->
	fprintf fmt "@\n(goto %s)" lab
    | JCPEcontinue lab ->
	fprintf fmt "@\n(continue %s)" lab
    | JCPEbreak lab ->
	fprintf fmt "@\n(break %s)" lab
    | JCPEwhile (e, behaviors, variant, s)->
	fprintf fmt "@\n@[loop %a%a@\nwhile (%a)%a@]"
	  (print_list nothing loop_behavior) behaviors
	  (print_option
             (fun fmt (t,r) ->
                match r with
                  | None ->
                      fprintf fmt "@\nvariant %a;" pexpr t
                  | Some r ->
                      fprintf fmt "@\nvariant %a for %a;" pexpr t identifier r
             ))
	  variant
	  pexpr e block [s]
    | JCPEfor (inits, cond, updates, behaviors, variant, body)->
	fprintf fmt "@\n@[loop %a@\n%a@\nfor (%a ; %a ; %a)%a@]"
	  (print_list nothing loop_behavior) behaviors
	  (print_option
             (fun fmt (t,r) ->
                match r with
                  | None ->
                      fprintf fmt "@\nvariant %a;" pexpr t
                  | Some r ->
                      fprintf fmt "@\nvariant %a for %a;" pexpr t identifier r
             ))
	  variant
	  (print_list comma pexpr) inits
	  pexpr cond (print_list comma pexpr) updates
	  block [body]
    | JCPEdecl (ty,vi, None)->
	fprintf fmt "@\n(var %a %s)" ptype ty vi
    | JCPEdecl (ty,vi, Some e)->
	fprintf fmt "@\n(var %a %s = %a)"
	  ptype ty vi pexpr e
    | JCPEassert(behav,asrt,a)->
	fprintf fmt "@\n(%a %a%a)"
	  asrt_kind asrt
	  (print_list_delim
	     (constant_string "for ") (constant_string ": ")
	     comma identifier)
	  behav
	  pexpr a
    | JCPEcontract(req,dec,behs,e) ->
	fprintf fmt "@\n@[<v 2>( ";
	Option_misc.iter
	  (fun e -> if is_not_true e then
	     fprintf fmt "requires %a;@\n" pexpr e) req;
	Option_misc.iter
	  (fun (t,r) -> match r with
	     | None -> fprintf fmt "decreases %a;@\n" pexpr t
	     | Some r -> fprintf fmt "decreases %a for %a;@\n"
		 pexpr t identifier r)
	  dec;
	List.iter (behavior fmt) behs;
	fprintf fmt "@\n{ %a@ })@]" pexpr e
    | JCPEblock l -> block fmt l
    | JCPEswitch (e, csl) ->
	fprintf fmt "@\n@[<v 2>switch (%a) {%a@]@\n}"
	  pexpr e (print_list nothing case) csl

and triggers fmt trigs =
  print_list_delim lsquare rsquare alt (print_list comma pexpr) fmt trigs

and ptag fmt tag =
  match tag#node with
    | JCPTtag id -> string fmt id#name
    | JCPTbottom -> string fmt "\\bottom"
    | JCPTtypeof e -> fprintf fmt "\\typeof(%a)" pexpr e

and handler fmt (ei,vio,s) =
  fprintf fmt "@\n@[<v 2>catch %s %s %a@]"
    ei#name vio
    pexpr s

and pexprs fmt l = print_list semi pexpr fmt l

and block fmt b =
  match b with
    | [] -> fprintf fmt "{()}"
    | _::_ ->
        fprintf fmt "@\n@[<v 0>{@[<v 2>  ";
        pexprs fmt b;
        fprintf fmt "@]@\n}@]"

and case fmt (c,sl) =
  let onecase fmt = function
    | Some c ->
	fprintf fmt "@\ncase %a:" pexpr c
    | None ->
	fprintf fmt "@\ndefault:"
  in
  fprintf fmt "%a%a" (print_list nothing onecase) c pexpr sl

and behavior fmt (_loc,id,throws,assumes,requires,assigns,allocates,ensures) =
  fprintf fmt "@\n@[<v 2>behavior %s:" id;
  Option_misc.iter
    (fun a ->
(*       Format.eprintf "Jc_poutput: assumes %a@." pexpr a;*)
       if is_not_true a then
         fprintf fmt "@\nassumes %a;" pexpr a) assumes;
  Option_misc.iter (fprintf fmt "@\nrequires %a;" pexpr) requires;
  Option_misc.iter
    (fun id -> fprintf fmt "@\nthrows %s;" id#name) throws;
  Option_misc.iter
    (fun (_,locs) -> fprintf fmt "@\nassigns %a;"
       (print_list_or_default "\\nothing" comma pexpr) locs)
    assigns;
  Option_misc.iter
    (fun (_,locs) -> fprintf fmt "@\nallocates %a;"
       (print_list_or_default "\\nothing" comma pexpr) locs)
    allocates;
  fprintf fmt "@\nensures %a;@]" pexpr ensures

and loop_behavior fmt (ids,inv,ass) =
  fprintf fmt "@\n@[<v 2>behavior %a:@\n"
    (print_list comma (fun fmt id -> fprintf fmt "%s" id#name)) ids;
  Option_misc.iter
    (fun i -> fprintf fmt "invariant %a;" pexpr i) inv;
  Option_misc.iter
    (fun (_,locs) -> fprintf fmt "@\nassigns %a;"
       (print_list_or_default "\\nothing" comma pexpr) locs)
    ass;
  fprintf fmt "@]"



let pclause fmt = function
  | JCCrequires e ->
      if is_not_true e then
	fprintf fmt "@\n@[<v 2>  requires @[%a@];@]" pexpr e
  | JCCdecreases(e,None) ->
      fprintf fmt "@\n@[<v 2>  decreases @[%a@];@]" pexpr e
  | JCCdecreases(e,Some r) ->
      fprintf fmt "@\n@[<v 2>  decreases @[%a@] for %a;@]"
	pexpr e identifier r
  | JCCbehavior b -> behavior fmt b

let param fmt (ty,vi) =
  fprintf fmt "%a %s" ptype ty vi

let fun_param fmt (valid,ty,vi) =
  fprintf fmt "%s%a %s" (if valid then "" else "! ") ptype ty vi

let field fmt (modifier,ty,fi,bitsize) =
  let (rep,abstract) = modifier in
  fprintf fmt "@\n";
  if abstract then
    fprintf fmt "abstract "
  else
    if rep then
      fprintf fmt "rep ";
  fprintf fmt "%a %s"
    ptype ty fi;
  match bitsize with
    | Some bitsize ->
	fprintf fmt ": %d;" bitsize
    | None ->
	fprintf fmt ";"

let invariant fmt (id, vi, a) =
  fprintf fmt "@\n@[<hv 2>invariant %s(%s) =@ %a;@]"
    id#name vi pexpr a

let reads_or_expr fmt = function
  | JCnone -> ()
  | JCreads [] ->
      fprintf fmt "@ reads \\nothing;"
  | JCreads el ->
      fprintf fmt "@ reads %a;" (print_list comma pexpr) el
  | JCexpr e ->
      fprintf fmt " =@\n%a" pexpr e
  | JCinductive l ->
      fprintf fmt " {@\n@[<v 2>%a@]@\n}"
	(print_list newline
	   (fun fmt (id,labels,e) ->
	      fprintf fmt "case %s@[%a@]: %a;@\n" id#name
		(print_list_delim lbrace rbrace comma label) labels
		pexpr e)) l

let type_params_decl fmt l = print_list_delim lchevron rchevron comma Pp.string fmt l

let type_params fmt = function
  | [] -> ()
  | l -> fprintf fmt "<%a>" (print_list comma ptype) l

let super_option fmt = function
  | None -> ()
  | Some(s, p) -> fprintf fmt "%s%a with " s type_params p

let rec pdecl fmt d =
  match d#node with
    | JCDfun(ty,id,params,clauses,body) ->
	fprintf fmt "@\n@[%a %s(@[%a@])%a%a@]@\n" ptype ty id#name
	  (print_list comma fun_param) params
	  (print_list nothing pclause) clauses
	  (print_option_or_default "\n;" pexpr) body
    | JCDenum_type(id,min,max) ->
	fprintf fmt "@\n@[type %s = %s..%s@]@\n"
	  id (Num.string_of_num min) (Num.string_of_num max)
    | JCDvariant_type(id, tags) ->
	fprintf fmt "@\n@[type %s = [" id;
	print_list
	  (fun fmt () -> fprintf fmt " | ")
	  (fun fmt tag -> fprintf fmt "%s" tag#name)
	  fmt tags;
	fprintf fmt "]@]@\n"
    | JCDunion_type(id,discriminated,tags) ->
	fprintf fmt "@\n@[type %s = [" id;
	print_list
	  (fun fmt () -> fprintf fmt " %c "
	     (if discriminated then '^' else '&'))
	  (fun fmt tag -> fprintf fmt "%s" tag#name)
	  fmt tags;
	fprintf fmt "]@]@\n"
    | JCDtag(id, params, super, fields, invs) ->
	fprintf fmt "@\n@[<v 2>tag %s%a = %a{%a%a@]@\n}@\n"
          id
          type_params_decl params
          super_option super
          (print_list space field) fields
	  (print_list space invariant) invs
    | JCDvar(ty,id,init) ->
	fprintf fmt "@\n@[%a %s%a;@]@\n" ptype ty id
	  (print_option (fun fmt e -> fprintf fmt " = %a" pexpr e)) init
    | JCDlemma(id,is_axiom,poly_args,lab,a) ->
	fprintf fmt "@\n@[%s %s@[%a@]@[%a@] :@\n%a@]@\n"
          (if is_axiom then "axiom" else "lemma") id
	  (print_list_delim lchevron rchevron comma string) poly_args
	  (print_list_delim lbrace rbrace comma label) lab
	  pexpr a
    | JCDglobal_inv(id,a) ->
	fprintf fmt "@\n@[invariant %s :@\n%a@]@\n" id pexpr a
    | JCDexception(id,tyopt) ->
	fprintf fmt "@\n@[exception %s of %a@]@\n" id
	  (print_option ptype) tyopt
    | JCDlogic_var (ty, id, body) ->
	fprintf fmt "@\n@[logic %a %s %a@]@\n"
	  ptype ty id
	  (print_option (fun fmt e -> fprintf fmt "=@\n%a" pexpr e)) body
    | JCDlogic (None, id, poly_args, labels, params, body) ->
	fprintf fmt "@\n@[predicate %s@[%a@]@[%a@](@[%a@])%a@]@\n"
	  id
          (print_list_delim lchevron rchevron comma string) poly_args
          (print_list_delim lbrace rbrace comma label) labels
	  (print_list comma param) params
	  reads_or_expr body
    | JCDlogic (Some ty, id, poly_args, labels, params, body) ->
	fprintf fmt "@\n@[logic %a %s@[%a@]@[%a@](@[%a@])%a@]@\n"
	  ptype ty id
          (print_list_delim lchevron rchevron comma string) poly_args
          (print_list_delim lbrace rbrace comma label) labels
	  (print_list comma param) params
	  reads_or_expr body
    | JCDlogic_type (id,args) ->
	fprintf fmt "@\n@[logic type %s%a@]@\n" id (print_list_delim lchevron rchevron comma string) args
    | JCDinvariant_policy p ->
        fprintf fmt "# InvariantPolicy = %s@\n" (string_of_invariant_policy p)
    | JCDseparation_policy p ->
        fprintf fmt "# SeparationPolicy = %s@\n" (string_of_separation_policy p)
    | JCDtermination_policy p ->
        fprintf fmt "# TerminationPolicy = %s@\n" (string_of_termination_policy p)
    | JCDannotation_policy p ->
        fprintf fmt "# AnnotationPolicy = %s@\n" (string_of_annotation_policy p)
    | JCDabstract_domain p ->
        fprintf fmt "# AbstractDomain = %s@\n" (string_of_abstract_domain p)
    | JCDint_model p ->
        fprintf fmt "# IntModel = %s@\n" (string_of_int_model p)
    | JCDpragma_gen_sep (kind,s,l) ->
        let print_ptype_r =
          print_pair ptype (print_list semi string) in
        fprintf fmt "# Gen_Separation %s %s(%a)\n" kind s
          (print_list comma print_ptype_r) l
    | JCDpragma_gen_frame (name,logic) ->
      fprintf fmt "# Gen_Frame %s %s" name logic
    | JCDpragma_gen_sub (name,logic) ->
      fprintf fmt "# Gen_Sub %s %s" name logic
    | JCDpragma_gen_same (name,logic) ->
      fprintf fmt "# Gen_Same_Footprint %s %s" name logic
    | JCDaxiomatic(id,l) ->
	fprintf fmt "@\n@[axiomatic %s {@\n@[<v 2>%a@]@\n}@]@\n" id
	  (print_list space pdecl) l

and pdecls fmt (l : pexpr decl list) =
  match l with
    | [] -> ()
    | d::r -> pdecl fmt d; pdecls fmt r

(*
Local Variables:
compile-command: "LC_ALL=C make -j -C .. byte"
End:
*)
