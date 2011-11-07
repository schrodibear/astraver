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

(** Ouput the normalized AST. Useful for debugging. Not parsable. *)

open Jc_pervasives
open Jc_output_misc
open Jc_ast
open Format
open Pp


let identifier fmt id =
  fprintf fmt "%s" id#name

let rec expr fmt e =
  let out x = fprintf fmt x in
  match e#node with
    | JCNEconst c ->
        const fmt c
    | JCNElabel(id, e1) ->
        out "(@[<hv 2>%s:@ %a@])" id expr e1
    | JCNEvar id ->
        out "%s" id
    | JCNEderef(e1, id) ->
        out "%a.%s" expr e1 id
    | JCNEbinary(e1, op, e2) ->
        out "(@[<hv 2>%a %s@ %a@])" expr e1 (string_of_op op) expr e2
    | JCNEunary(op, e1) ->
        out "(%s %a)" (string_of_op op) expr e1
    | JCNEapp(id, labs, el) ->
        out "@[<hv 2>%s@,{%a}@,(%a)@]" id (print_list comma label)
          labs (print_list comma expr) el
    | JCNEassign(e1, e2) ->
        out "(@[<hv 2>%a =@ %a@])" expr e1 expr e2
    | JCNEinstanceof(_e1, _id) ->
        out "(TODO instanceof)"
    | JCNEcast(_e1, _id) ->
        out "(TODO cast)"
    | JCNEif(_e1, _e2, _e3) ->
        out "(TODO if)"
    | JCNEoffset(k, e1) ->
        out "(\\offset_m%a(%a))" offset_kind k expr e1
    | JCNEaddress(absolute,e1) ->
        out "(\\%aaddress(%a))" address_kind absolute expr e1
    | JCNEbase_block(e1) ->
        out "(\\base_block(%a))" expr e1
    | JCNEfresh(e1) ->
        out "(\\fresh(%a))" expr e1
    | JCNEalloc(_e1, _id) ->
        out "(TODO alloc)"
    | JCNEfree _e1 ->
        out "(TODO free)"
    | JCNElet(Some pty, id, Some e1, e2) ->
        out "(@[<hv 2>let %a %s = %a in@ %a@])" ptype pty id expr e1 expr e2
    | JCNElet(Some pty, id, None, e1) ->
        out "(@[<hv 2>let %a %s in@ %a@])" ptype pty id expr e1
    | JCNElet(None, id, Some e1, e2) ->
        out "(@[<hv 2>let %s = %a in@ %a@])" id expr e1 expr e2
    | JCNElet(None, id, None, e1) ->
        out "(@[<hv 2>let %s in@ %a@])" id expr e1
    | JCNEassert (behav,asrt,e1) ->
        out "(%a %a%a)" 
	  asrt_kind asrt
	  (print_list_delim 
	     (constant_string "for ") (constant_string ": ") 
	     comma identifier)
	  behav
	  expr e1
    | JCNEcontract _ -> assert false (* TODO *)
    | JCNEblock el ->
        out "{@ @[<hv 2>%a@]@ }" (print_list semi expr) el
    | JCNEloop(_inv, Some _e2, _e3) ->
	out "(some loop)" (* TODO *)
	  (*
        out "@[<hv 2>%a@ variant %a;@ %a done@]" 
	  (print_list nothing 
	     (fun fmt (behav,inv) -> out "@\ninvariant %a%a;"
		(print_list_delim 
		   (constant_string "for ") (constant_string ": ") 
		   comma string)
		behav
		expr inv))
	  inv
	  expr e2
          expr e3
	  *)
    | JCNEloop(_inv, None, _e2) ->
        out "(some loop)" (* TODO *)
	  (*
	    out "@[<hv 2>%a@ %a done@]" 
	  (print_list nothing 
	     (fun fmt (behav,inv) -> out "@\ninvariant %a%a;"
		(print_list_delim 
		   (constant_string "for ") (constant_string ": ") 
		   comma string)
		behav
		expr inv))
	  inv
	  expr e2
	  *)
    | JCNEreturn(Some e1) ->
        out "(return %a)" expr e1
    | JCNEreturn None ->
        out "(return)"
    | JCNEtry(e1, l, e2) ->
        out "(@[<hv 2>try %a with@ %a@ | default -> %a@])" expr e1
          (print_list space
             (fun fmt (id, s, e3) ->
                fprintf fmt "| %s %s -> %a" id#name s expr e3))
          l expr e2
    | JCNEthrow(id, Some e1) ->
        out "(throw %s %a)" id#name expr e1
    | JCNEthrow(id, None) ->
        out "(throw %s)" id#name
    | JCNEpack(_e1, _ido) ->
        out "(TODO pack)"
    | JCNEunpack(_e1, _ido) ->
        out "(TODO unpack)"
    | JCNEmatch(_e1, _pel) ->
        out "(TODO match)"
    | JCNEquantifier(Forall, pty, idl, trigs, e1) ->
        out "(@[<hv 2>\\forall %a %a %a,@ %a@])" ptype pty
          (print_list space identifier) idl
          triggers trigs expr e1
    | JCNEquantifier(Exists, pty, idl, trigs, e1) ->
        out "(@[<hv 2>\\exists %a %a%a,@ %a@])" ptype pty
          (print_list space identifier) idl 
           triggers trigs expr e1
    | JCNEold _e1 ->
        out "(TODO old)"
    | JCNEat(e1, lab) ->
        out "\\at(%a,@ %a)" expr e1 label lab
    | JCNEmutable(_e1, _tag) ->
        out "(TODO mutable)"
    | JCNEeqtype(_tag1, _tag2) ->
        out "(TODO eqtype)"
    | JCNEsubtype(_tag1, _tag2) ->
        out "(TODO subtype)"
    | JCNErange(Some e1, Some e2) ->
        out "(%a .. %a)" expr e1 expr e2
    | JCNErange(Some e1, None) ->
        out "(%a ..)" expr e1
    | JCNErange(None, Some e1) ->
        out "(.. %a)" expr e1
    | JCNErange(None, None) ->
        out "(..)"

and triggers fmt trigs = 
  print_list_delim lsquare rsquare alt (print_list comma expr) fmt trigs

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
