(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
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

(* $Id: jc_poutput.ml,v 1.5 2008-03-20 16:05:13 moy Exp $ *)

open Format
open Jc_env
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Pp

let ptype fmt t =
  match t.jc_ptype_node with
    | JCPTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCPTidentifier s -> string fmt s
    | JCPTpointer (name,ao, bo) ->
	begin match ao, bo with
	  | None, None ->
	      fprintf fmt "%s[..]" name
	  | Some a, None ->
	      fprintf fmt "%s[%s..]" name (Num.string_of_num a)
	  | None, Some b ->
	      fprintf fmt "%s[..%s]" name (Num.string_of_num b)
	  | Some a, Some b ->
	      if Num.eq_num a b then
		fprintf fmt "%s[%s]" name (Num.string_of_num a)
	      else
		fprintf fmt "%s[%s..%s]" name
		  (Num.string_of_num a) (Num.string_of_num b)
	end

let const fmt c =
  match c with
    | JCCinteger s -> fprintf fmt "%s" s
    | JCCreal s -> fprintf fmt "%s" s
    | JCCboolean b -> fprintf fmt "%B" b
    | JCCnull -> fprintf fmt "null"
    | JCCvoid -> fprintf fmt "()"

let pbin_op = function
  | BPlt -> "<"
  | BPgt -> ">"
  | BPle -> "<="
  | BPge -> ">="
  | BPeq -> "=="
  | BPneq -> "!="
  | BPadd -> "+"
  | BPsub -> "-"
  | BPmul -> "*"
  | BPdiv -> "/"
  | BPmod -> "%"
  | BPland -> "&&"
  | BPlor -> "||"
  | BPimplies -> "==>"
  | BPiff -> "<==>"
  | BPbw_and -> "&"
  | BPbw_or -> "|"
  | BPbw_xor -> "^"
  | BPlogical_shift_right -> ">>"
  | BParith_shift_right -> ">>>"
  | BPshift_left -> "<<"

let punary_op = function
  | UPplus -> "+"
  | UPminus -> "-"
  | UPnot -> "!"
  | UPpostfix_inc | UPprefix_inc -> "++"
  | UPpostfix_dec | UPprefix_dec -> "--"
  | UPbw_not -> "~"

let offset_kind fmt k =
  match k with
    | Offset_max -> fprintf fmt "ax"
    | Offset_min -> fprintf fmt "in"

let real_conversion fmt rc =
  match rc with
    | Integer_to_real -> fprintf fmt "real"
    | Real_to_integer -> fprintf fmt "integer"

let label fmt l =
  match l with
    | LabelName s -> fprintf fmt "%s" s.label_info_name
    | LabelHere -> fprintf fmt "Here" 
    | LabelPre -> fprintf fmt "Pre" 
    | LabelOld -> fprintf fmt "Old" 
    | LabelPost -> fprintf fmt "Post" 

let rec ppattern fmt p =
  match p.jc_ppattern_node with
    | JCPPstruct(st, lbls) ->
	fprintf fmt "@[<hv 2>%s{@ " st.jc_identifier_name;
	List.iter
	  (fun (lbl, pat) ->
	     fprintf fmt "%s = %a;@ " lbl.jc_identifier_name ppattern pat)
	  lbls;
	fprintf fmt "}@]"
    | JCPPvar vi ->
	fprintf fmt "%s" vi.jc_identifier_name
    | JCPPor(p1, p2) ->
	fprintf fmt "(%a)@ | (%a)" ppattern p1 ppattern p2
    | JCPPas(pat, vi) ->
	fprintf fmt "(%a as %s)" ppattern pat vi.jc_identifier_name
    | JCPPany ->
	fprintf fmt "_"
    | JCPPconst c ->
	fprintf fmt "%a" const c

let quantifier fmt = function
  | Forall -> fprintf fmt "forall"
  | Exists -> fprintf fmt "exists"

let rec pexpr fmt e =
  match e.jc_pexpr_node with
    | JCPElabel(lab,e) ->
	assert (lab <> "");
	fprintf fmt "@[(%s : %a)@]" lab pexpr e
    | JCPEconst c -> const fmt c
    | JCPEvar vi -> 
	fprintf fmt "%s" vi
    | JCPEbinary (e1, op, e2) ->
	fprintf fmt "@[(%a %s %a)@]" pexpr e1 (pbin_op op) pexpr e2
    | JCPEunary((UPpostfix_dec | UPpostfix_inc) as op,e1) ->
	fprintf fmt "@[(%a %s)@]" pexpr e1 (punary_op op) 
    | JCPEunary(op,e1) ->
	fprintf fmt "@[(%s %a)@]" (punary_op op) pexpr e1 
    | JCPEif (e1,e2,e3) -> 
	fprintf fmt "@[(%a ? %a : %a)@]" pexpr e1 pexpr e2 pexpr e3
    | JCPElet(vi,e1,e2) -> 
	fprintf fmt "@[(let %s =@ %a@ in %a)@]" 
	  vi pexpr e1 pexpr e2 
    | JCPEassign (v, e) -> 
	fprintf fmt "(%a = %a)" pexpr v pexpr e
    | JCPEassign_op (v, op, e) -> 
	fprintf fmt "%a %s= %a" pexpr v (pbin_op op) pexpr e
    | JCPEcast (e, si) ->
	fprintf fmt "(%a :> %s)" pexpr e si
    | JCPEalloc (e, si) ->
	fprintf fmt "(new %s[%a])" si pexpr e 
    | JCPEfree (e) ->
	fprintf fmt "(free(%a))" pexpr e 
    | JCPEoffset(k,e) ->
	fprintf fmt "\\offset_m%a(%a)" offset_kind k pexpr e 
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
    | JCPEquantifier (q,ty,vil, a)-> 
	fprintf fmt "@[<v 3>(\\%a %a %a;@\n%a)@]"
	  quantifier q
	  ptype ty
	  (print_list comma string) vil
	  pexpr a
    | JCPEmutable _ -> assert false (* TODO *)
    | JCPEtagequality _ -> assert false (* TODO *)

let pclause fmt = function
  | JCPCrequires e -> 
      fprintf fmt "@\n@[<v 2>  requires @[%a@];@]" pexpr e
  | JCPCbehavior(_loc,id,throws,assumes,requires,assigns,ensures) ->
      fprintf fmt "@\n@[<v 2>behavior %s:" id;
      Option_misc.iter (fprintf fmt "@\nassumes %a;" pexpr) assumes;
      Option_misc.iter (fprintf fmt "@\nrequires %a;" pexpr) requires;
      Option_misc.iter 
	(fun id -> fprintf fmt "@\nthrows %s;" id.jc_identifier_name) throws;
      Option_misc.iter 
	(fun (_,locs) -> fprintf fmt "@\nassigns %a;" 
	  (print_list_or_default "\\nothing" comma pexpr) locs)
	assigns;
      fprintf fmt "@\nensures %a;@]" pexpr ensures
  
let rec pstatement fmt s =
  match s.jc_pstatement_node with
    | JCPSskip -> string fmt ";"
    | JCPSreturn (e) ->
	fprintf fmt "@\nreturn %a;" (print_option pexpr) e
    | JCPSunpack _ -> assert false (* TODO *) 
    | JCPSpack _ -> assert false (* TODO *) 
    | JCPSthrow (ei, eo) ->
	fprintf fmt "@\nthrow %s %a;" 
	  ei.jc_identifier_name 
	  (print_option_or_default "()" pexpr) eo
    | JCPStry (s, hl, fs) ->
	fprintf fmt 
	  "@\n@[<v 2>try %a@]%a@\n@[<v 2>finally%a@]"
	  pstatement s 
	  (print_list nothing handler) hl
	  pstatement fs
    | JCPSgoto lab -> 
	fprintf fmt "@\ngoto %s;" lab
    | JCPSlabel (lab, s) -> 
	fprintf fmt "@\n%s:%a" lab pstatement s
    | JCPScontinue lab -> 
	fprintf fmt "@\ncontinue %s;" lab
    | JCPSbreak lab -> 
	fprintf fmt "@\nbreak %s;" lab
    | JCPSwhile (lab, e, invariant,variant, s)-> 
	fprintf fmt "@\n@[%s@\ninvariant %a;%a@\nwhile (%a)%a@]"
	  (if lab = "" then "" else lab ^ ": ")
	  pexpr invariant 
	  (print_option (fun fmt t -> fprintf fmt "@\nvariant %a;" pexpr t))
	  variant
	  pexpr e block [s]
    | JCPSfor (lab,inits, cond, updates, invariant,variant, body)-> 
	fprintf fmt "@\n@[%s@\ninvariant %a;%a@\nfor (%a ; %a ; %a)%a@]"
	  (if lab = "" then "" else lab ^ ": ")
	  pexpr invariant 
	  (print_option (fun fmt t -> fprintf fmt "@\nvariant %a;" pexpr t))
	  variant
	  (print_list comma pexpr) inits 
	  pexpr cond (print_list comma pexpr) updates
	  block [body]
    | JCPSif (e, s1, s2) ->
	fprintf fmt "@\n@[<v 2>if (%a) %a@]@\n@[<v 2>else %a@]"
	  pexpr e pstatement s1 pstatement s2
    | JCPSdecl (ty,vi, None)-> 
	fprintf fmt "@\n%a %s;" ptype ty vi
    | JCPSdecl (ty,vi, Some e)-> 
	fprintf fmt "@\n%a %s = %a;" 
	  ptype ty vi pexpr e
    | JCPSassert(a)-> 
	fprintf fmt "@\nassert %a;" pexpr a
    | JCPSexpr e -> fprintf fmt "@\n%a;" pexpr e
    | JCPSblock l -> block fmt l
    | JCPSswitch (e, csl) ->
	fprintf fmt "@\n@[<v 2>switch (%a) {%a@]@\n}"
	  pexpr e (print_list nothing case) csl
    | JCPSmatch (e, psl) ->
	fprintf fmt "@[<v 2>match %a with@ " pexpr e;
	List.iter
	  (fun (p, s) -> fprintf fmt "  @[<v 2>%a -> {@ %a@ @]}@ "
	     ppattern p block s) psl;
	fprintf fmt "end@]"
	
and case fmt (c,sl) =
  let onecase fmt = function
    | Some c ->
	fprintf fmt "@\ncase %a:" pexpr c
    | None ->
	fprintf fmt "@\ndefault:"
  in
  fprintf fmt "%a%a" (print_list nothing onecase) c block sl

and handler fmt (ei,vio,s) =
  fprintf fmt "@\n@[<v 2>catch %s %s %a@]"
    ei.jc_identifier_name vio
    pstatement s

and pstatements fmt l = List.iter (pstatement fmt) l

and block fmt b =
  fprintf fmt "@\n@[<v 0>{@[<v 2>  ";
  pstatements fmt b;
  fprintf fmt "@]@\n}@]"


let param fmt (ty,vi) =
  fprintf fmt "%a %s" ptype ty vi

let field fmt (rep,ty,fi) =
  fprintf fmt "@\n";
  if rep then
    fprintf fmt "rep ";
  fprintf fmt "%a %s;" 
    ptype ty fi

let invariant fmt (id, vi, a) =
  fprintf fmt "@\ninvariant %s(%s) = %a;"
    id.jc_identifier_name vi pexpr a

let reads_or_expr fmt = function
  | JCPReads [] -> 
      fprintf fmt "reads \\nothing;"
  | JCPReads el -> 
      fprintf fmt "reads %a;" (print_list comma pexpr) el
  | JCPExpr e -> 
      fprintf fmt "=@\n%a" pexpr e

let rec pdecl fmt d =
  match d.jc_pdecl_node with
    | JCPDrecfuns _ -> assert false
    | JCPDfun(ty,id,params,clauses,body) ->
	fprintf fmt "@\n@[%a %s(@[%a@])%a%a@]@." ptype ty id.jc_identifier_name
	  (print_list comma param) params 
	  (print_list nothing pclause) clauses
	  (print_option_or_default "\n;" block) body
    | JCPDenumtype(id,min,max) ->
	fprintf fmt "@\n@[type %s = %s..%s@]@."
	  id (Num.string_of_num min) (Num.string_of_num max)
    | JCPDvarianttype(id, tags) ->
	fprintf fmt "@\n@[type %s = [" id;
	print_list
	  (fun fmt () -> fprintf fmt " | ")
	  (fun fmt tag -> fprintf fmt "%s" tag.jc_identifier_name)
	  fmt tags;
	fprintf fmt "]@]@."
    | JCPDuniontype(id, tags) ->
	fprintf fmt "@\n@[type %s = [" id;
	print_list
	  (fun fmt () -> fprintf fmt " & ")
	  (fun fmt tag -> fprintf fmt "%s" tag.jc_identifier_name)
	  fmt tags;
	fprintf fmt "]@]@."
    | JCPDtag (id, extends, fields, invs) ->
	fprintf fmt "@\n@[<v 2>tag %s = %a{%a%a@]@\n}@."
	  id (print_option string) extends (print_list space field) fields 
	  (print_list space invariant) invs
    | JCPDvar(ty,id,init) ->
	fprintf fmt "@\n@[%a %s%a;@]@." ptype ty id
	  (print_option (fun fmt e -> fprintf fmt " = %a" pexpr e)) init
    | JCPDlemma(id,is_axiom,lab,a) ->
	fprintf fmt "@\n@[%s %s" (if is_axiom then "axiom" else "lemma") id;
	if lab <> [] then 
	  fprintf fmt "%a" 
	    (print_list_delim lbrace rbrace comma label) lab;
	fprintf fmt " :@\n%a@]@." pexpr a
    | JCPDglobinv(id,a) ->
	fprintf fmt "@\n@[invariant %s :@\n%a@]@." id pexpr a
    | JCPDexception(id,ty) ->
	fprintf fmt "@\n@[exception %s of %a@]@." id
	  ptype ty
    | JCPDlogic (None, id, labels, params, body) ->
	fprintf fmt "@\n@[logic %s%a(@[%a@]) %a@]@." 
	  id (print_list_delim lbrace rbrace comma label) labels
	  (print_list comma param) params
	  reads_or_expr body 
    | JCPDlogic (Some ty, id, labels, params, body) ->
	fprintf fmt "@\n@[logic %a %s%a(@[%a@]) %a@]@." 
	  ptype ty 
	  id (print_list_delim lbrace rbrace comma label) labels
	  (print_list comma param) params
	  reads_or_expr body 
    | JCPDlogictype id ->
	fprintf fmt "@\n@[logic type %s@]@." id
   
let rec pdecls fmt d =
  match d with
    | [] -> ()
    | d::r -> pdecl fmt d; pdecls fmt r

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte bin/krakatoa.byte"
End: 
*)
