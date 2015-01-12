(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

open Stdlib

open Format
open Env
open Ast
open Fenv
open Common
open Constructors
open Print_misc
open Why_pp

type jc_decl =
  | JCfun_def of jc_type * string * (bool * var_info) list *
      fun_spec * expr option
  | JCenum_type_def of string * Num.num * Num.num
  | JCvariant_type_def of string * string list
  | JCunion_type_def of string * string list
  | JCstruct_def of string * string option * field_info list *
      (string * var_info * assertion) list
  | JCrec_struct_defs of jc_decl list
      (* deprecated, all tag definitions of a file are mutually recursive *)
  | JCrec_fun_defs of jc_decl list
  | JCvar_def of jc_type * string * expr option
  | JClemma_def of string * bool * type_var_info list * label list * assertion
  | JClogic_fun_def of jc_type option * string * type_var_info list * label list
      * var_info list * term_or_assertion
  | JCexception_def of string * exception_info
  | JCglobinv_def of string * assertion
  | JClogic_const_def of jc_type * string * type_var_info list * term option
  | JClogic_type_def of string * type_var_info list
  | JCinvariant_policy of Env.inv_sem
  | JCseparation_policy of Env.separation_sem
  | JCannotation_policy of Env.annotation_sem
  | JCabstract_domain of Env.abstract_domain
  | JCint_model of Env.int_model
  | JCfloat_rounding_mode of Env.float_rounding_mode
  | JCfloat_model of Env.float_model
  | JCfloat_instruction_set of string
  | JCtermination_policy of Env.termination_policy

(*
let lbin_op op =
  if op == Pervasives.ge_int then ">=" else
  if op == Pervasives.le_int then "<=" else
  if op == Pervasives.gt_int then ">" else
  if op == Pervasives.lt_int then "<" else
  if op == Pervasives.eq then "==" else
  if op == Pervasives.neq then "!=" else
  if op == Pervasives.add_int then "+" else
  if op == Pervasives.sub_int then "-" else
  if op == Pervasives.mul_int then "*" else
  if op == Pervasives.div_int then "/" else
  if op == Pervasives.mod_int then "%" else
  if op == Pervasives.shift then "+" else
  raise Not_found
*)

let identifier fmt id =
  fprintf fmt "%s" id#name

let type_var_info fmt x = fprintf fmt "%s" (Type_var.uname x)

let bin_op (op, _) = match op with
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

let unary_op (op, _) = match op with
  | `Uminus -> "-"
  | `Unot -> "!"
  | `Ubw_not -> "~"

let real_conversion fmt rc =
  match rc with
    | Integer_to_real -> fprintf fmt "real"
    | Double_to_real -> fprintf fmt "double_value"
    | Float_to_real -> fprintf fmt "single_value"
    | Round(_f,_m) -> (* fprintf fmt "r_to_s" ou "r_to_" *)
         (* TODO ? parameter rounding mode *)
	assert false

let rec pattern fmt p =
  match p#node with
    | JCPstruct(st, lbls) ->
	fprintf fmt "@[<hv 2>%s{@ " st.si_name;
	List.iter
	  (fun (lbl, pat) ->
	     fprintf fmt "%s = %a;@ " lbl.fi_name pattern pat)
	  lbls;
	fprintf fmt "}@]"
    | JCPvar vi ->
	fprintf fmt "%s" vi.vi_name
    | JCPor(p1, p2) ->
	fprintf fmt "(%a)@ | (%a)" pattern p1 pattern p2
    | JCPas(pat, vi) ->
	fprintf fmt "(%a as %s)" pattern pat vi.vi_name
    | JCPany ->
	fprintf fmt "_"
    | JCPconst c ->
	fprintf fmt "%a" const c

let rec term fmt t =
  if t#mark <> "" then
    fprintf fmt "@[(%s : %a)@]"
      t#mark term (new term_with ~mark:"" t)
  else
  match t#node with
    | JCTvar vi -> fprintf fmt "%s" vi.vi_name
    | JCTbinary(t1,op,t2) ->
	fprintf fmt "@[(%a %s %a)@]" term t1 (bin_op op) term t2
    | JCTunary(op,t1) ->
	fprintf fmt "@[(%s %a)@]" (unary_op op) term t1
    | JCTif (t1,t2,t3) ->
	fprintf fmt "@[(%a ? %a : %a)@]" term t1 term t2 term t3
    | JCTlet (vi,t1,t2) ->
	fprintf fmt "@[(let %s = %a in %a)@]"
          vi.vi_name term t1 term t2
    | JCTcast (t, _, si)
    | JCTbitwise_cast (t, _, si) ->
	fprintf fmt "(%a :> %s)" term t si.si_name
    | JCTrange_cast (t, ei) ->
	fprintf fmt "(%a :> %s)" term t (Option.map_default ~default:"integer" ~f:(fun r -> r.ei_name) ei)
    | JCTreal_cast (t, rc) ->
	fprintf fmt "(%a :> %a)" term t real_conversion rc
    | JCTinstanceof (t, _, si) ->
	fprintf fmt "(%a <: %s)" term t si.si_name
    | JCToffset (k,t,_)->
	fprintf fmt "@[\\offset_m%a(%a)@]" offset_kind k term t
    | JCTaddress(absolute,t) ->
	fprintf fmt "@[\\%aaddress(%a)@]" address_kind absolute term t
    | JCTbase_block (t)->
	fprintf fmt "@[\\base_block(%a)@]" term t
    | JCTold t -> fprintf fmt "@[\\old(%a)@]" term t
    | JCTat(t,lab) -> fprintf fmt "@[\\at(%a,%a)@]" term t label lab
(*
    | JCTapp app when List.length app.app_args = 1 ->
	let op = app.app_fun in
	let t1 = List.hd app.app_args in
	begin try
	  ignore
	    (Hashtbl.find Typing.enum_conversion_logic_functions_table op);
	  (* conversion due to enumeration. Ignore it. *)
	  term fmt t1
	with Not_found ->
	  fprintf fmt "%s(@[%a@])" op.li_name term t1
	end
    | JCTapp app when List.length app.app_args = 2 ->
	let op = app.app_fun in
	let l = app.app_args in
	  begin try
	  let s = lbin_op op in
	  fprintf fmt "@[(%a %s %a)@]" term t1 s term t2
	with Not_found ->
	  fprintf fmt "@[%s(%a)@]" op.li_name
	    (print_list comma term) l
	end
*)
    | JCTapp app ->
	let op = app.app_fun and l = app.app_args in
	fprintf fmt "%s(@[%a@])" op.li_name
	  (print_list comma term) l
    | JCTderef (t, _label, fi)->
	fprintf fmt "@[%a.%s@]" term t fi.fi_name
    | JCTshift (t1, t2) ->
	fprintf fmt "@[(%a + %a)@]" term t1 term t2
    | JCTconst c -> const fmt c
    | JCTrange (t1,t2) ->
	fprintf fmt "@[[%a..%a]@]" (print_option term) t1 (print_option term) t2
    | JCTmatch (t, ptl) ->
	fprintf fmt "@[<v 2>match %a with@ " term t;
	List.iter
	  (fun (p, t) -> fprintf fmt "  @[<v 2>%a ->@ %a;@]@ "
	     pattern p term t) ptl;
	fprintf fmt "end@]"

let quantifier = Print_p.quantifier

let rec assertion fmt a =
  if a#mark <> "" then
    fprintf fmt "@[(%s : %a)@]"
      (a#mark) assertion
      (new assertion_with ~mark:"" a)
  else
  match a#node with
    | JCAtrue -> fprintf fmt "true"
    | JCAif (t, a1, a2) ->
	fprintf fmt "@[(%a ? %a : %a)@]" term t assertion a1 assertion a2
    | JCAbool_term t -> term fmt t
    | JCAinstanceof (t, _lab, st) ->
	fprintf fmt "(%a <: %s)" term t st.si_name
    | JCAfresh t -> fprintf fmt "\\fresh(%a)" term t
    | JCAold a -> fprintf fmt "\\old(%a)" assertion a
    | JCAat(a,lab) -> fprintf fmt "\\at(%a,%a)" assertion a label lab
    | JCAquantifier (q,vi, trigs, a)->
	fprintf fmt "@[(\\%a %a %s%a;@\n%a)@]"
	  quantifier q
	  print_type vi.vi_type
	  vi.vi_name
          triggers trigs
	  assertion a
    | JCArelation (t1, op, t2) ->
	fprintf fmt "@[(%a %s %a)@]" term t1 (bin_op op) term t2
    | JCAapp app ->
	 fprintf fmt "@[%s(%a)@]" app.app_fun.li_name
	      (print_list comma term) app.app_args
    | JCAnot a1 ->
	fprintf fmt "@[(!@ %a)@]" assertion a1
    | JCAiff (a1, a2)->
	fprintf fmt "@[(%a <==>@ %a)@]" assertion a1 assertion a2
    | JCAimplies (a1, a2)->
	fprintf fmt "@[(%a ==>@ %a)@]" assertion a1 assertion a2
    | JCAor [] -> assert false
    | JCAor (a::l) ->
	fprintf fmt "@[(%a" assertion a;
	List.iter
	  (fun a -> fprintf fmt " ||@ %a" assertion a)
	  l;
	fprintf fmt ")@]"
    | JCAand [] -> assert false
    | JCAand (a::l) ->
	fprintf fmt "@[(%a" assertion a;
	List.iter
	  (fun a -> fprintf fmt " &&@ %a" assertion a)
	  l;
	fprintf fmt ")@]"
    | JCAfalse -> fprintf fmt "false"
    | JCAmutable _ ->
        fprintf fmt "mutable(TODO)"
    | JCAeqtype _ -> assert false (* TODO *)
    | JCAsubtype _ -> assert false (* TODO *)
    | JCAlet (vi, t, p) ->
	fprintf fmt "@[<v 2>let %s =@ %a in@ %a@]" vi.vi_name
          term t
	  assertion p
    | JCAmatch (t, pal) ->
	fprintf fmt "@[<v 2>match %a with@ " term t;
	List.iter
	  (fun (p, a) -> fprintf fmt "  @[<v 2>%a ->@ %a;@]@ "
	     pattern p assertion a) pal;
	fprintf fmt "end@]"

and triggers fmt trigs =
  let pat fmt = function
  | JCAPatT t -> term fmt t
  | JCAPatP p -> assertion fmt p in
  print_list_delim lsquare rsquare semi (print_list comma pat) fmt trigs


let rec location_set fmt locs =
  match locs#node with
    | JCLSvar vi->
	fprintf fmt "%s" vi.vi_name
    | JCLSderef (locs, _, fi, _) ->
	fprintf fmt "%a.%s" location_set locs fi.fi_name
    | JCLSrange (locset, t1, t2) ->
	fprintf fmt "(%a + [%a..%a])" location_set locset
	  (print_option term) t1 (print_option term) t2
    | JCLSrange_term (locset, t1, t2) ->
	fprintf fmt "(%a + [%a..%a])" term locset
	  (print_option term) t1 (print_option term) t2
    | JCLSat(locset,lab) ->
	fprintf fmt "\\at(%a, %a)" location_set locset label lab

let rec location fmt loc =
  match loc#node with
    | JCLvar vi ->
	fprintf fmt "%s" vi.vi_name
    | JCLderef (locs, _, fi,_) ->
	fprintf fmt "%a.%s" location_set locs fi.fi_name
    | JCLderef_term (t1, fi) ->
	fprintf fmt "%a.%s" term t1 fi.fi_name
    | JCLat (loc, lab) ->
	fprintf fmt "\\at(%a,%a)" location loc label lab

let behavior fmttr (_loc, id, b) =
  let open Option in
  let pr fmt = fprintf fmttr fmt in
  pr "@\n@[<v 2>behavior %s:" id;
  iter b.b_assumes ~f:(pr "@\nassumes %a;" assertion);
  iter b.b_throws ~f:(fun a -> pr "@\nthrows %s;" a.exi_name);
  iter b.b_assigns ~f:(snd %> pr "@\nassigns %a;" (print_list_or_default "\\nothing" comma location));
  pr "@\nensures %a;@]" assertion b.b_ensures

let print_spec fmttr s =
  let open Option in
  let pr fmt = fprintf fmttr fmt in
  pr "@\n@[<v 2>  requires @[%a@];" assertion s.fs_requires;
  iter
    s.fs_decreases
    ~f:(fun (t, r) ->
       match r with
       | None -> pr "@\n@[<v 2>  decreases @[%a@];" term t
       | Some li -> pr "@\n@[<v 2>  decreases @[%a@] for %s;" term t li.li_name);
  List.iter (behavior fmttr) (s.fs_default_behavior :: s.fs_behavior);
  pr "@]"

let call_bin_op _op =
  raise Not_found

let rec expr fmt e =
  if e#mark <> "" then
    fprintf fmt "@[(%s : %a)@]"
      e#mark expr (new expr_with ~mark:"" e)
  else
    match e#node with
      | JCEconst c -> const fmt c
      | JCEvar vi ->
	  fprintf fmt "%s" vi.vi_name
      | JCEderef(e, fi) ->
	  fprintf fmt "%a.%s" expr e fi.fi_name
      | JCEbinary(e1, op, e2) ->
	  fprintf fmt "@[(%a %s %a)@]" expr e1 (bin_op op) expr e2
      | JCEunary(op,e1) ->
	  fprintf fmt "@[(%s %a)@]" (unary_op op) expr e1
      | JCEassign_var(v, e) ->
	  fprintf fmt "(%s = %a)" v.vi_name expr e
      | JCEassign_heap(e1, fi, e2) ->
	  fprintf fmt "%a.%s = %a" expr e1 fi.fi_name expr e2
      | JCEinstanceof(e, si) ->
	  fprintf fmt "(%a <: %s)" expr e si.si_name
      | JCEcast(e, si)
      | JCEbitwise_cast(e, si) ->
	  fprintf fmt "(%a :> %s)" expr e si.si_name
      | JCErange_cast(e, ri) ->
	  fprintf fmt "(%a :> %s)" expr e (Option.map_default ~f:(fun r -> r.ei_name) ~default:"integer" ri)
      | JCEreal_cast(e, rc) ->
	  fprintf fmt "(%a :> %a)" expr e real_conversion rc
      | JCEif(e1,e2,e3) ->
	  fprintf fmt "@[(%a ? %a : %a)@]" expr e1 expr e2 expr e3
      | JCEoffset(k,e, _) ->
	  fprintf fmt "\\offset_m%a(%a)" offset_kind k expr e
      | JCEaddress(absolute,e) ->
	  fprintf fmt "\\%aaddress(%a)" address_kind absolute expr e
      | JCEbase_block(e) ->
	  fprintf fmt "\\base_block(%a)" expr e
      | JCEfresh(e) ->
	  fprintf fmt "\\fresh(%a)" expr e
      | JCEalloc(e, si) ->
	  fprintf fmt "(new %s[%a])" si.si_name expr e
      | JCEfree e ->
	  fprintf fmt "(free(%a))" expr e
      | JCEreinterpret (e, si) ->
          fprintf fmt "(reinterpret %a as %s)" expr e si.si_name
      | JCElet(vi,Some e1,e2) ->
	  fprintf fmt "@[(let %s =@ %a@ in %a)@]"
	    vi.vi_name expr e1 expr e2
      | JCElet(vi,None,e2) ->
	  fprintf fmt "@[%a %s; %a@]"
	    print_type vi.vi_type vi.vi_name expr e2
      | JCEassert(behav,asrt,a) ->
	  fprintf fmt "@\n%a %a%a;"
	    asrt_kind asrt
	    (print_list_delim
	       (constant_string "for ") (constant_string ": ")
	       comma identifier)
	    behav
	    assertion a
      | JCEcontract(_req,_dec,_vi_result,_behs,_e) ->
	  assert false (* TODO *)
      | JCEblock l ->
          block fmt l
      | JCEreturn_void ->
	  fprintf fmt "@\nreturn;"
      | JCEreturn(_, e) ->
	  fprintf fmt "@\nreturn %a;" expr e
      | JCEtry(s, hl, fs) ->
	  fprintf fmt
	    "@\n@[<v 2>try %a@]%a@\n@[<v 2>finally%a@]"
	    expr s
	    (print_list nothing handler) hl
	    expr fs
      | JCEthrow(ei, eo) ->
	  fprintf fmt "@\nthrow %s %a;"
	    ei.exi_name
	    (print_option_or_default "()" expr) eo
      | JCEpack _ ->
          fprintf fmt "pack(TODO)"
      | JCEunpack _ ->
          fprintf fmt "unpack(TODO)"
      | JCEmatch(e, pel) ->
	  fprintf fmt "@[<v 2>match %a with@ " expr e;
	  List.iter
	    (fun (p, e) -> fprintf fmt "  @[<v 2>%a ->@ %a;@]@ "
	       pattern p expr e) pel;
	  fprintf fmt "end@]"
      | JCEshift(e1, e2) ->
	  fprintf fmt "@[(%a + %a)@]" expr e1 expr e2
      | JCEloop(la, e) ->
          fprintf fmt "@\n@[%a%a@\nwhile (true)%a@]"
	  (print_list nothing loop_behavior)
(*
	     (fun fmt (behav,inv) -> fprintf fmt "@\ninvariant %a%a;"
		(print_list_delim
		   (constant_string "for ") (constant_string ": ")
		   comma string)
		behav
		assertion inv))
*)
	    la.loop_behaviors
            (print_option
               (fun fmt (t,r) ->
                  match r with
                    | None -> fprintf fmt "@\nvariant %a;" term t
                    | Some r -> fprintf fmt "@\nvariant %a for %s;" term t
                        r.li_name
               ))
            la.loop_variant
            expr e
      | JCEapp{ call_fun = (JClogic_fun{ li_final_name = name }
                | JCfun{ fun_final_name = name });
                call_args = args } ->
          fprintf fmt "@[%s(%a)@]" name
            (print_list comma expr) args

and loop_behavior fmttr (ids, inv, ass) =
  let open Option in
  let pr fmt = fprintf fmttr fmt in
  pr "@\n@[<v 2>behavior %a:@\n"  (print_list comma (fun fmt id -> fprintf fmt "%s" id#name)) ids;
  iter inv ~f:(pr "invariant %a;" assertion) ;
  iter ass ~f:(pr "@\nassigns %a;" @@ print_list_or_default "\\nothing" comma location);
  pr "@]"

and case fmt (c,sl) =
  let onecase fmt = function
    | Some c ->
	fprintf fmt "@\ncase %a:" expr c
    | None ->
	fprintf fmt "@\ndefault:"
  in
  fprintf fmt "%a%a" (print_list nothing onecase) c block sl

and handler fmt (ei,vio,s) =
  fprintf fmt "@\n@[<v 2>catch %s %a %a@]"
    ei.exi_name
    (print_option_or_default "__dummy"
      (fun fmt vi -> fprintf fmt "%s" vi.vi_name)) vio
    expr s

and statements fmt l = List.iter (expr fmt) l

and block fmt b =
  fprintf fmt "@\n@[<v 0>{@[<v 2>  ";
  statements fmt b;
  fprintf fmt "@]@\n}@]"


let param fmt vi =
  fprintf fmt "%a %s" print_type vi.vi_type vi.vi_name

let fun_param fmt (valid,vi) =
  fprintf fmt "%s%a %s"
    (if valid then "" else "!")
    print_type vi.vi_type vi.vi_name

let field fmt fi =
  fprintf fmt "@\n";
  if fi.fi_rep then
    fprintf fmt "rep ";
  fprintf fmt "%a %s"
    print_type fi.fi_type fi.fi_name;
  match fi.fi_bitsize with
    | Some bitsize ->
	fprintf fmt ": %d;" bitsize
    | None ->
	fprintf fmt ";"

let invariant fmt (id, vi, a) =
  fprintf fmt "@\n@[invariant %s(%s) =@ %a;@]"
    id vi.vi_name assertion a

let term_or_assertion fmt = function
  | JCAssertion a ->
      fprintf fmt "=@\n%a" assertion a
  | JCTerm t ->
      fprintf fmt "=@\n%a" term t
  | JCNone ->
      fprintf fmt ";"
  | JCReads [] ->
      fprintf fmt "reads \\nothing;"
  | JCReads locs ->
      fprintf fmt "reads %a;" (print_list comma location) locs
  | JCInductive l ->
      fprintf fmt "{@\n@[<v 2>%a@]@\n}"
	(print_list newline
	   (fun fmt (id,labels,e) ->
	      fprintf fmt "case %s" id#name ;
	      if labels <> [] then
		fprintf fmt "%a"
		  (print_list_delim lbrace rbrace comma label) labels;
	      fprintf fmt ": %a;@\n"
		assertion e)) l



let print_super fmt = function
  | None -> ()
  | Some id -> fprintf fmt "%s with " id

(*
let string_of_invariant_policy p =
  match p with
    | Env.InvNone -> "None"
    | Env.InvArguments -> "Arguments"
    | Env.InvOwnership -> "Ownership"

let string_of_separation_policy p =
  match p with
    | Env.SepNone -> "None"
    | Env.SepRegions -> "Regions"

let string_of_annotation_policy p =
  match p with
    | Env.AnnotNone -> "None"
    | Env.AnnotInvariants -> "Invariants"
    | Env.AnnotElimPre -> "ElimPre"
    | Env.AnnotStrongPre -> "StrongPre"
    | Env.AnnotWeakPre -> "WeakPre"

let string_of_abstract_domain p =
  match p with
    | Env.AbsNone -> "None"
    | Env.AbsBox -> "Box"
    | Env.AbsOct -> "Oct"
    | Env.AbsPol -> "Pol"

let string_of_int_model p =
  match p with
    | Env.IMbounded -> "bounded"
    | Env.IMmodulo -> "modulo"
*)

let string_of_float_rounding_mode p =
  match p with
    | Env.FRMNearestEven -> "nearesteven"
    | Env.FRMDown -> "down"
    | Env.FRMUp -> "up"
    | Env.FRMToZero -> "tozero"
    | Env.FRMNearestAway -> "nearestaway"

let string_of_float_model p =
  match p with
    | Env.FMmath -> "math"
    | Env.FMdefensive -> "defensive"
    | Env.FMfull-> "full"
    | Env.FMmultirounding-> "multirounding"

let rec print_decl fmt d =
  match d with
    | JCinvariant_policy p ->
        fprintf fmt "# InvariantPolicy = %s@\n" (string_of_invariant_policy p)
    | JCseparation_policy p ->
        fprintf fmt "# SeparationPolicy = %s@\n" (string_of_separation_policy p)
    | JCannotation_policy p ->
        fprintf fmt "# AnnotationPolicy = %s@\n" (string_of_annotation_policy p)
    | JCtermination_policy p ->
        fprintf fmt "# TerminationPolicy = %s@\n" (string_of_termination_policy p)
    | JCabstract_domain p ->
        fprintf fmt "# AbstractDomain = %s@\n" (string_of_abstract_domain p)
    | JCint_model p ->
        fprintf fmt "# IntModel = %s@\n" (string_of_int_model p)
    | JCfloat_model p ->
        fprintf fmt "# FloatModel = %s@\n" (string_of_float_model p)
    | JCfloat_rounding_mode p ->
        fprintf fmt "# FloatRoundingMode = %s@\n" (string_of_float_rounding_mode p)
    | JCfloat_instruction_set p ->
        fprintf fmt "# FloatInstructionSet = %s@\n" p
    | JCfun_def(ty,id,params,spec,body) ->
	fprintf fmt "@\n@[%a %s(@[%a@])%a%a@]@." print_type ty id
	  (print_list comma fun_param) params
	  print_spec spec
	  (print_option_or_default "\n;" expr) body
    | JCenum_type_def(id,min,max) ->
	fprintf fmt "@\n@[type %s = %s..%s@]@."
	  id (Num.string_of_num min) (Num.string_of_num max)
    | JCvariant_type_def(id, tags) ->
	fprintf fmt "@\n@[type %s = [" id;
	print_list
	  (fun fmt () -> fprintf fmt " | ")
	  (fun fmt tag -> fprintf fmt "%s" tag)
	  fmt tags;
	fprintf fmt "]@]@."
    | JCunion_type_def(id, tags) ->
	fprintf fmt "@\n@[type %s = [" id;
	print_list
	  (fun fmt () -> fprintf fmt " & ")
	  (fun fmt tag -> fprintf fmt "%s" tag)
	  fmt tags;
	fprintf fmt "]@]@."
    | JCstruct_def (id, extends, fields, invs) ->
	fprintf fmt "@\n@[<v 2>tag %s = %a{%a%a@]@\n}@."
	  id print_super extends (print_list space field) fields
	  (print_list space invariant) invs
    | JCrec_struct_defs dlist | JCrec_fun_defs dlist ->
	print_list (fun _fmt () -> ()(*fprintf fmt "@\nand"*))
	  print_decl fmt dlist
    | JCvar_def(ty,id,init) ->
	fprintf fmt "@\n@[%a %s%a;@]@." print_type ty id
	  (print_option (fun fmt e -> fprintf fmt " = %a" expr e)) init
    | JClemma_def(id,is_axiom,poly_args,lab,a) ->
	fprintf fmt "@\n@[%s %s%a%a :@\n%a@]@."
          (if is_axiom then "axiom" else "lemma") id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
          (print_list_delim lbrace rbrace comma label) lab
          assertion a
    | JCglobinv_def(id,a) ->
	fprintf fmt "@\n@[invariant %s :@\n%a@]@." id assertion a
    | JCexception_def(id,ei) ->
	fprintf fmt "@\n@[exception %s of %a@]@." id
	  (print_option_or_default "unit" print_type)
	  ei.exi_type
    | JClogic_const_def(ty,id,poly_args,None) ->
	fprintf fmt "@\n@[logic %a %s%a@]@." print_type ty id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args

    | JClogic_const_def(ty,id,poly_args,Some t) ->
	fprintf fmt "@\n@[logic %a %s%a = %a@]@." print_type ty id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
	  term t
    | JClogic_fun_def(None,id,poly_args,labels,[],JCReads l) ->
	assert (l=[]);
	assert (labels=[]);
	fprintf fmt "@\n@[predicate %s@[%a@]@]@."
	  id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
    | JClogic_fun_def(Some ty,id,poly_args,labels,[],JCReads l) ->
	assert (l=[]);
	assert (labels=[]);
	fprintf fmt "@\n@[logic %a %s@[%a@]@]@."
	  print_type ty id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
(* Yannick: no need for different rule for const logic *)
(*     | JClogic_fun_def(ty,id,labels,[],JCTerm t) -> *)
(* 	assert (labels=[]); *)
(* 	fprintf fmt "@\n@[logic %a %s = %a@]@."  *)
(* 	  (print_option print_type) ty id term t *)
(*    | JClogic_fun_def(ty,id,poly_args,[],params,body) ->
	fprintf fmt "@\n@[logic %a %s@[%a@](@[%a@]) %a@]@."
	  (print_option print_type) ty id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
          (print_list comma param) params
	  term_or_assertion body *)
    | JClogic_fun_def (None, id, poly_args, labels, params, body) ->
	fprintf fmt "@\n@[predicate %s%a%a(@[%a@]) %a@]@."
	  id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
          (print_list_delim lbrace rbrace comma label) labels
	  (print_list comma param) params
	  term_or_assertion body
    | JClogic_fun_def (Some ty, id, poly_args, labels, params, body) ->
	fprintf fmt "@\n@[logic %a %s%a%a(@[%a@]) %a@]@."
	  print_type ty id
          (print_list_delim lchevron rchevron comma type_var_info) poly_args
          (print_list_delim lbrace rbrace comma label) labels
	  (print_list comma param) params
	  term_or_assertion body
    | JClogic_type_def (id,args) ->
	fprintf fmt "@\n@[logic type %s%a@]@." id
          (print_list_delim lchevron rchevron comma type_var_info) args

let rec print_decls fmt d =
  match d with
    | [] -> ()
    | d::r -> print_decl fmt d; print_decls fmt r


(*
Local Variables:
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte bin/krakatoa.byte"
End:
*)