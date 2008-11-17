(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jc_norm.ml,v 1.111 2008-11-17 15:48:29 marche Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_pervasives
open Jc_constructors
open Jc_ast
open Format
open Jc_iterators
open Jc_constructors.PExpr


(** Normalization: transforms the parsed AST in order to reduce the number of
    constructs. As it works on untyped expressions, the transformations are
    all syntax-oriented:
    - transform switch into sequence of ifs with exceptions
    - transform while and for into loop with gotos
    - transform op-assign into normal assign and op
    - transform gotos into exceptions *)


(**************************************************************************)
(* Globals to add to the list of declarations                             *)
(**************************************************************************)

let name_for_loop_exit = Jc_envset.get_unique_name "Loop_exit"
let name_for_loop_continue = Jc_envset.get_unique_name "Loop_continue"
let name_for_return_label = get_unique_name "Return_label"

let loop_exit = new identifier name_for_loop_exit
let loop_continue = new identifier name_for_loop_continue
let return_label = new identifier name_for_return_label

let label_to_exception = Hashtbl.create 17

let goto_exception_for_label lab =
  (* CIL defines a label "return_label" to go to before returning. 
     It is recognized here so that static analysis recognizes these returns
     and avoids merging all returns together. *)
  if lab = "return_label" then return_label else
    try
      Hashtbl.find label_to_exception lab 
    with Not_found ->
      let excname = Jc_envset.get_unique_name ("Goto_" ^ lab) in
      let exc = new identifier excname in
      Hashtbl.add label_to_exception lab exc;
      exc


(**************************************************************************)
(* Transformations                                                        *)
(**************************************************************************)

(** Transform switch *)
let normalize_switch pos e caselist =
  (* Give a temporary name to the switch expression, so that modifying
   * a variable on which this expression depends does not interfere 
   * with the control-flow, when its value is tested.
   *)
  let epos = e#pos in
  let tmpname = tmp_var_name () in
  let tmpvar = mkvar ~pos:epos ~name:tmpname () in
  let has_default c = List.exists (fun c -> c = None) c in
  (* Test for case considered *)
  let test_one_case ~(neg:bool) c = 
    let op = if neg then `Bneq else `Beq in
    mkbinary ~pos:epos ~expr1:tmpvar ~op ~expr2:c ()
  in
  (* Collect negative tests for [default] case *)
  let all_neg_cases () = 
    let collect_neg_case c = 
      List.fold_right (fun c l -> match c with
			 | Some c -> test_one_case ~neg:true c :: l
			 | None -> l) c []
    in
    fst (List.fold_left (fun (l,after_default) (c,_)  -> 
			   if after_default then
			     collect_neg_case c @ l,after_default
			   else		
			     l,has_default c
			) ([],false) caselist)
  in
  let test_one_case_or_default = function
    | Some c -> test_one_case ~neg:false c
    | None -> mkand ~pos:epos ~list:(all_neg_cases ()) ()
  in
  let test_case_or_default c = 
    mkor ~pos:epos ~list:(List.map test_one_case_or_default c) ()
  in
  let rec cannot_fall_trough e = 
    match e#node with
      | JCPEblock [] -> 
	  false
      | JCPEblock elist -> 
	  cannot_fall_trough (List.hd (List.rev elist))
      | JCPEthrow _ | JCPEreturn _ | JCPEwhile _ | JCPEfor _ -> 
	  true
      | JCPEif(_,te,fe) ->
	  cannot_fall_trough te && cannot_fall_trough fe
      | _ -> false
  in
  let rec fold_case (previous_c,acc) = 
    function [] -> List.rev acc | (c,e) :: next_cases ->
      (* No need to test on previous values if default present *)
      let current_c = if has_default c then c else previous_c @ c in
      let teste = test_case_or_default current_c in
      (* Case translated into if-statement *)
      if cannot_fall_trough e then
	let nexte = start_fold_case next_cases in
	let ife =
          mkif ~pos:epos ~condition:teste ~expr_then:e ~expr_else:nexte () in
	List.rev (ife :: acc)
      else
	let ife = mkif ~pos:epos ~condition:teste ~expr_then:e () in
	fold_case (current_c, ife :: acc) next_cases
  and start_fold_case caselist = 
    let iflist = fold_case ([],[]) caselist in
    mkblock ~pos ~exprs:iflist ()
  in
  let iflist = fold_case ([],[]) caselist in
  let switche = mkblock ~pos ~exprs:iflist () in
  let catche = [mkcatch ~pos ~name:(tmp_var_name()) ~exn:loop_exit ()] in
  let trye = mktry ~pos ~expr:switche ~catches:catche () in
  mklet_nodecl ~var:tmpname ~init:e ~body:trye ()

(** Transform while-loop *)
let normalize_while pos test inv var body =
  let body = match test#node with
    | JCPEconst(JCCboolean true) -> body
	(* Special case of an infinite loop [while(true)].
	 * Then, no condition needs to be tested. This form is expected
	 * for some assertions to be recognized as loop invariants
	 * later on, in annotation inference. *)
    | _ ->
	let exit_ = mkthrow ~pos ~exn:loop_exit () in
	mkif ~pos ~condition:test ~expr_then:body ~expr_else:exit_ ()
  in
  mktry ~pos
    ~expr:
    (mkwhile ~pos ~invariant:inv ?variant:var 
       ~body:
       (mktry ~pos 
          ~expr:
          (mkblock ~pos ~exprs:[body; mkthrow ~pos ~exn:loop_continue ()] ())
	  ~catches: [mkcatch ~pos ~name:(tmp_var_name()) ~exn:loop_continue ()]
          ())
       ())
    ~catches:
    [mkcatch ~pos ~name:(tmp_var_name()) ~exn:loop_exit ()]
    ()

(** Transform for-loop *)
let normalize_for pos inits test updates inv var body =
  mkblock ~pos
    ~exprs:(inits 
	    @ [mktry ~pos
                 ~expr:
		 (mkwhile ~pos ~invariant:inv ?variant:var 
                    ~body:
		    (mktry ~pos 
                       ~expr:
		       (mkblock ~pos ~exprs:[
			  mkif ~pos ~condition:test ~expr_then:body 
                            ~expr_else:(mkthrow ~pos ~exn:loop_exit ()) ();
			  mkthrow ~pos ~exn:loop_continue ()] ())
                       ~catches:
		       [mkcatch ~pos ~name:(tmp_var_name()) ~exn:loop_continue
                          ~body:(mkblock ~pos ~exprs:updates ()) ()] ())
                    ())
                 ~catches:
		 [mkcatch ~pos ~name:(tmp_var_name()) ~exn:loop_exit ()]
                 ()
	      ])
    ()
    
let duplicable =
  IPExpr.fold_left 
    (fun acc e -> acc && match e#node with
       | JCPEconst _ | JCPEvar _ | JCPErange _ | JCPEderef _
       | JCPEunary _ | JCPEoffset _ | JCPEaddress _ | JCPEold _ | JCPEat _
       | JCPEbinary _ | JCPEcast _ | JCPEsubtype _ | JCPEbase_block _ ->
	   true
       | JCPEassert _ | JCPEthrow _ | JCPEreturn _ | JCPEeqtype _  
       | JCPEbreak _ | JCPEcontinue _  | JCPEgoto _  | JCPEdecl _
       | JCPElabel _ | JCPEinstanceof _ | JCPEalloc _ 
       | JCPEfree _ | JCPElet _ | JCPEpack _ | JCPEunpack _ 
       | JCPEquantifier _ | JCPEmutable _ | JCPEassign _ 
       | JCPEassign_op _ | JCPEif _ | JCPEwhile _ | JCPEblock _
       | JCPEapp _ | JCPEtry _ | JCPEmatch _ | JCPEfor _
       | JCPEswitch _ | JCPEcontract _ ->
	   false
    ) true

(** Transform assign-op *)
let normalize_assign_op pos e1 op e2 =
  if duplicable e1 then
    mkassign
      ~pos
      ~location:e1
      ~value:(mkbinary ~pos ~expr1:e1 ~op ~expr2:e2 ())
      ()
  else
    match e1#node with
      | JCPEderef(e3,f) ->
	  let tmpname = tmp_var_name () in
	  let tmpvar = mkvar ~pos ~name:tmpname () in
	  let e4 = mkderef ~pos ~expr:tmpvar ~field:f () in
	  mklet_nodecl
            ~var:tmpname
            ~init:e3
	    ~body:
            (mkassign
               ~pos
               ~location:e4
               ~value:(mkbinary ~pos ~expr1:e4 ~op ~expr2:e2 ())
               ())
            ()
      | _ -> Jc_options.jc_error pos "Not an lvalue in assignment"

(** Transform unary increment and decrement *)
let normalize_pmunary pos op e =
  let op_of_incdec = function
    | `Uprefix_inc | `Upostfix_inc -> `Badd 
    | `Uprefix_dec | `Upostfix_dec -> `Bsub
    | `Uplus -> assert false
  in
  let on_duplicable e =
    match op with
      | `Uprefix_inc | `Uprefix_dec ->
	  (* e = e +/- 1 } *)
	  mkassign
            ~pos
            ~location: e
            ~value:
            (mkbinary
               ~pos
               ~expr1: e
               ~op: (op_of_incdec op)
               ~expr2: (mkint ~pos ~value:1 ())
               ())
            ()
      | `Upostfix_inc | `Upostfix_dec ->
	  let tmpname = tmp_var_name () in
	  let tmpvar = mkvar ~pos ~name:tmpname () in
	  (* let tmp = e in { e = tmp +/- 1; tmp } *)
	  mklet_nodecl
            ~var: tmpname
            ~init: e
            ~body:
	    (mkblock ~pos ~exprs:[
	       mkassign ~pos ~location:e
		 ~value:
                 (mkbinary
                    ~pos
                    ~expr1:tmpvar
                    ~op:(op_of_incdec op)
                    ~expr2:(mkint ~pos ~value:1 ())
                    ())
                 ();
	       tmpvar
	     ] ())
            ()
      | `Uplus -> assert false
  in
  match op with `Uplus -> e | _ ->
    if duplicable e then on_duplicable e else 
      match e#node with
	| JCPEderef(e1,f) ->
	    let tmpname = tmp_var_name () in
	    let tmpvar = mkvar ~pos ~name:tmpname () in
	    let e2 = mkderef ~pos ~expr:tmpvar ~field:f () in
	    mklet_nodecl ~var:tmpname ~init:e1 ~body:(on_duplicable e2) ()
	| _ -> Jc_options.jc_error pos "Not an lvalue in assignment"

(** Transform local variable declarations *)
let normalize_locvardecl pos elist = 
  mkblock ~pos
    ~exprs:
    (List.fold_right
       (fun e acc ->
	  match e#node with
	    | JCPEdecl(ty,name,initopt) ->
		[mklet_nodecl ~pos:e#pos ~typ:ty ~var:name ?init:initopt
                   ~body:(mkblock ~pos ~exprs:acc ()) ()]
	    | JCPElabel(lab, e1) ->
                begin match e1#node with
                  | JCPEdecl(ty,name,initopt) ->
                      [mklabel
                         ~pos:e#pos
                         ~label:lab (*(mkskip e#pos);*)
                         ~expr:
                         (mklet_nodecl
                            ~pos: e#pos
                            ~typ: ty
                            ~var: name
                            ?init: initopt
                            ~body: (mkblock ~pos ~exprs:acc ())
                            ())
                         ()]
                  | _ -> e::acc
                end
	    | _ -> e::acc
       ) elist []
    )
    ()

let normalize_postaction pos elist =
  let pre_of_post = function
    | `Upostfix_inc -> `Uprefix_inc
    | `Upostfix_dec -> `Uprefix_dec
  in
  mkblock ~pos 
    ~exprs:
    (match List.rev elist with [] -> elist | last::elist' ->
       (* Only transform into pre increment/decrement those post increment/
	* decrement whose value is discarded, like all expressions in a block
	* but the last one.
	*)
       (List.fold_left (fun acc e -> match e#node with
			  | JCPEunary(#post_unary_op as op,e') -> 
			      new pexpr_with 
				~node:(JCPEunary(pre_of_post op,e')) e
			      :: acc
			  | _ -> e :: acc
		       ) [last] elist'
       ))
    ()

(** Apply normalizations recursively *)
let normalize = 
  map_pexpr 
    ~before:(fun e -> match e#node with
	       | JCPEblock elist ->
		   normalize_postaction e#pos elist
	       | _ -> e
	    )
    ~after:(fun e -> match e#node with
	      | JCPEassign_op(e1,op,e2) -> 
		  normalize_assign_op e#pos e1 op e2
	      | JCPEunary(#pm_unary_op as op,e') -> 
		  normalize_pmunary e#pos op e'
	      | JCPEswitch(e',caselist) -> 
		  normalize_switch e#pos e' caselist
	      | JCPEwhile(test,inv,var,body) ->
		  normalize_while e#pos test inv var body
	      | JCPEfor(inits,test,updates,inv,var,body) ->
		  normalize_for e#pos inits test updates [[],inv] var body
	      | JCPEbreak lab ->
		  assert (lab = ""); (* TODO for Java *)
		  mkthrow ~pos:e#pos ~exn:loop_exit ()
	      | JCPEcontinue lab ->
		  assert (lab = ""); (* TODO for Java *)
		  mkthrow ~pos:e#pos ~exn:loop_continue ()
	      | JCPEblock elist ->
		  normalize_locvardecl e#pos elist
	      | _ -> e
	   )

(** Transform gotos *)
(* Build the structure of labels in a function body, using Huet's
   zipper, so as to identify 'structured' gotos, i.e., those gotos that
   go forward and do not enter scopes.
*)

let label_used = Hashtbl.create 17

type label_tree =
  | LabelItem of string
  | LabelBlock of label_tree list

let rec printf_label_tree fmt lt =
  match lt with 
    | LabelItem s -> fprintf fmt "%s" s
    | LabelBlock l -> 
	fprintf fmt "{ %a }" (Pp.print_list Pp.space printf_label_tree ) l

let rec in_label_tree lab = function
  | LabelItem l -> l=lab
  | LabelBlock l -> in_label_tree_list lab l

and in_label_tree_list lab = function
  | [] -> false
  | h::r -> 
      in_label_tree lab h || in_label_tree_list lab r

let rec in_label_upper_tree_list lab = function
  | [] -> false
  | LabelItem l :: _ when l=lab -> true
  | _ :: r -> in_label_upper_tree_list lab r

let build_label_tree e : label_tree list =
  (* [acc] is the tree of labels for the list of statements that follow 
     the current one, in the same block.
     [fwdacc] is the tree of labels for all the statements that follow 
     the current one to the end of the function. It is used to identify
     unused labels.
  *)
  let rec build_bwd e (acc,fwdacc) =
    match e#node with
      | JCPEgoto lab ->
	  (* Count number of forward gotos. Labels with 0 count will
	     not be considered in generated try-catch. *)
	  if in_label_upper_tree_list lab fwdacc then
	    Hashtbl.add label_used lab ()
	  else 
	    Jc_options.jc_error e#pos "unsupported goto (backward or to some inner block)";
	  acc,fwdacc
      | JCPElabel (lab, e) ->
	  let l,fwdl = build_bwd e ([],fwdacc) in
	  (LabelItem lab) :: (LabelBlock l) :: acc, (LabelItem lab) :: fwdl
      | JCPEblock sl ->
	  let l,fwdl = List.fold_right build_bwd sl ([],fwdacc) in
	  (LabelBlock l) :: acc, fwdl
      | _ ->
	  let elist = IPExpr.subs e in
	  LabelBlock 
	    (List.map (fun e -> LabelBlock(fst (build_bwd e ([],fwdacc)))) elist)
	  :: acc, fwdacc
  in
  fst (build_bwd e ([],[]))

let goto_block pos el =
  let rec label_block el = 
    match el with [] -> [],[] | e1::r ->
      let elr,labelr = label_block r in
      match e1#node with
	| JCPElabel(lab,e2) when Hashtbl.mem label_used lab ->
	    let e3 = mkblock ~pos ~exprs:(e2::elr) () in
	    let e4 = mklabel ~pos ~label:lab ~expr:e3 () in
	    [],(lab,[e4])::labelr
	| _ -> e1::elr,labelr
  in
  let el,labels = label_block el in
  let el = List.fold_left (fun acc (lab,el) ->
		    let id = goto_exception_for_label lab in
		    (* Throw expression in case of fall-through *)
		    let throw = mkthrow ~pos ~exn:id () in
		    [mktry ~pos
                       ~expr:(mkblock ~pos ~exprs:(acc@[throw]) ())
		       ~catches:
                       [mkcatch ~pos ~name:(tmp_var_name()) ~exn:id 
			  ~body:(mkblock ~pos ~exprs:el ()) ()]
                       ()
		    ]
		 ) el labels
  in
  mkblock ~pos ~exprs:el ()

let rec goto e lz =
  let pos = e#pos in
  let enode,lz2 = match e#node with
    | JCPEgoto lab -> 
	let id = goto_exception_for_label lab in
	JCPEthrow(id, mkvoid ()), lz
    | JCPElabel (lab,e1) ->
	let lz1 = match lz with
	  | LabelItem lab'::LabelBlock b1::after ->
	      assert (lab=lab');
	      b1@after
	  | _ -> assert false
	in
	let e2, lz2 = goto e1 lz1 in
	JCPElabel(lab,e2), lz2
    | JCPEblock el -> 
	let lz1,lz2 = match lz with
	  | LabelBlock b1::after ->
	      b1@after,after
	  | _ -> assert false
	in
	let el,_ = 
	  List.fold_left (fun (acc,lz1) e1 ->
			    let e2,lz2 = goto e1 lz1 in e2::acc,lz2
			 ) ([],lz1) el
	in
	let el = List.rev el in
	(goto_block pos el)#node, lz2
    | _ ->
	let elist = IPExpr.subs e in
	let lz1list,lz2 = match lz with
	  | LabelBlock b1::after ->
	      List.map
		(function LabelBlock b -> b@after | _ -> assert false) b1,
	      after
	  | _ -> assert false
	in
	let elist,_ = List.split (List.map2 goto elist lz1list) in
	(replace_sub_pexpr e elist)#node, lz2
  in new pexpr_with ~node:enode e, lz2


(**************************************************************************)
(* Translation                                                            *)
(**************************************************************************)

(** From parsed expression to normalized expression *)
let rec expr e =
  let enode = match e#node with
    | JCPEconst c -> JCNEconst c
    | JCPElabel(id,e) -> JCNElabel(id,expr e)
    | JCPEvar id -> JCNEvar id
    | JCPEderef(e,id) -> JCNEderef(expr e,id)
    | JCPEbinary(e1,op,e2) -> JCNEbinary(expr e1,op,expr e2)
    | JCPEunary(#unary_op as op,e) -> JCNEunary(op,expr e)
    | JCPEunary _ -> assert false
    | JCPEapp(id,lablist,elist) -> JCNEapp(id,lablist,List.map expr elist)
    | JCPEassign(e1,e2) -> JCNEassign(expr e1,expr e2)
    | JCPEassign_op _ -> assert false
    | JCPEinstanceof(e,id) -> JCNEinstanceof(expr e,id)
    | JCPEcast(e,id) -> JCNEcast(expr e,id)
    | JCPEquantifier(q,ty,idlist,e) -> JCNEquantifier(q,ty,idlist,expr e)
    | JCPEold e -> JCNEold(expr e)
    | JCPEat(e,lab) -> JCNEat(expr e,lab)
    | JCPEoffset(off,e) -> JCNEoffset(off,expr e)
    | JCPEaddress(absolute,e) -> JCNEaddress(absolute,expr e)
    | JCPEbase_block(e) -> JCNEbase_block(expr e)
    | JCPEif(e1,e2,e3) -> JCNEif(expr e1,expr e2,expr e3)
    | JCPElet(tyopt,id,e1,e2) -> 
	JCNElet(tyopt,id,Option_misc.map expr e1,expr e2)
    | JCPEdecl _ ->
	assert false
	(* (ty,name,initopt) ->  *)
(* 	JCNElet(Some ty,name,Option_misc.map expr initopt,expr (mkvoid())) *)
    | JCPErange(e1opt,e2opt) -> 
	JCNErange(Option_misc.map expr e1opt,Option_misc.map expr e2opt)
    | JCPEalloc(e,id) -> JCNEalloc(expr e,id)
    | JCPEfree e -> JCNEfree(expr e)
    | JCPEmutable(e,tag) -> JCNEmutable(expr e,tag_ tag)
    | JCPEeqtype(tag1,tag2) -> JCNEeqtype(tag_ tag1,tag_ tag2)
    | JCPEsubtype(tag1,tag2) -> JCNEsubtype(tag_ tag1,tag_ tag2)
    | JCPEmatch(e,pelist) ->
	JCNEmatch(expr e,List.map (fun (pat,e) -> (pat,expr e)) pelist)  
    | JCPEblock elist -> JCNEblock(List.map expr elist)
    | JCPEassert(behav,asrt,e) -> JCNEassert(behav,asrt,expr e)
    | JCPEcontract(req,dec,behs,e) -> 
	JCNEcontract(Option_misc.map expr req,
		     Option_misc.map expr dec,
		     List.map behavior behs,
		     expr e)
    | JCPEwhile(_,inv,vareopt,e) ->
	let inv = List.map (fun (behav,e) -> behav,expr e) inv in
	JCNEloop(inv,Option_misc.map expr vareopt,expr e)
    | JCPEfor _ -> assert false
    | JCPEreturn e ->
        begin match e#node with
          | JCPEconst JCCvoid -> JCNEreturn None
          | _ -> JCNEreturn(Some(expr e))
        end
    | JCPEbreak _ -> assert false
    | JCPEcontinue _ -> assert false
    | JCPEgoto _ -> assert false
    | JCPEtry(e,hlist,fe) ->
	let hlist = List.map (fun (id1,id2,e) -> (id1,id2,expr e)) hlist in
	JCNEtry(expr e,hlist,expr fe)
    | JCPEthrow(id, e) ->
	JCNEthrow(id, Some(expr e))
    | JCPEpack(e,idopt) -> JCNEpack(expr e,idopt)
    | JCPEunpack(e,idopt) -> JCNEunpack(expr e,idopt)
    | JCPEswitch _ -> assert false
  in
  new nexpr ~pos:e#pos enode

and tag_ tag = 
  let tagnode = match tag#node with
    | JCPTtypeof e -> JCPTtypeof (expr e)
    | JCPTtag _ | JCPTbottom as tagnode -> tagnode
  in
  new ptag ~pos:tag#pos tagnode

and behavior (pos,id,idopt,e1opt,e2opt,asslist,e3) =
  (pos,id,idopt,
   Option_misc.map expr e1opt,
   Option_misc.map expr e2opt,
   Option_misc.map (fun (pos,elist) -> pos,List.map expr elist) asslist,
   expr e3)

let expr e =
  let e,_ = goto e (build_label_tree e) in
  let e = expr (normalize e) in
  (*
    let fmt = Format.std_formatter in
    Format.fprintf fmt "Normalized expression:@\n%a@\n@."
    Jc_noutput.expr e;
  *)
  e

(** From parsed clause to normalized clause *)
let clause = function
  | JCCrequires e -> JCCrequires(expr e)
  | JCCbehavior b -> JCCbehavior(behavior b)

    
(** From parsed reads-or-expr to normalized reads-or-expr *)
let reads_or_expr = function
  | JCreads elist -> JCreads(List.map expr elist)
  | JCexpr e -> JCexpr(expr e)
(*
  | JCaxiomatic l -> JCaxiomatic(List.map (fun (id,e) -> (id, expr e)) l)
*)
  | JCinductive l -> JCinductive(List.map (fun (id,e) -> (id, expr e)) l)
    
(** From parsed declaration to normalized declaration *)
let rec decl d = 
  let dnode = match d#node with
    | JCDfun(ty,id,params,clauses,body) ->
	JCDfun(ty,id,params,List.map clause clauses,Option_misc.map expr body)
    | JCDenum_type(id,min,max) ->
	JCDenum_type(id,min,max)
    | JCDvariant_type(id, tags) ->
	JCDvariant_type(id, tags)
    | JCDunion_type(id,discr,tags) ->
	JCDunion_type(id,discr,tags)
    | JCDtag (id, params, extends, fields, invs) ->
	JCDtag (id, params, extends, fields, 
		List.map (fun (id,name,e) -> id,name,expr e) invs)
    | JCDvar(ty,id,init) ->
	JCDvar(ty,id,Option_misc.map expr init)
    | JCDlemma(id,is_axiom,lab,a) ->
	JCDlemma(id,is_axiom,lab,expr a)
    | JCDglobal_inv(id,a) ->
	JCDglobal_inv(id,expr a)
    | JCDexception(id,ty) ->
	JCDexception(id,ty)
    | JCDlogic_var (ty, id, body) ->
	JCDlogic_var (ty, id, Option_misc.map expr body)
    | JCDlogic (ty, id, labels, params, body) ->
	JCDlogic (ty, id, labels, params, reads_or_expr body)
    | JCDlogic_type id ->
	JCDlogic_type id
    | JCDint_model x -> JCDint_model x
    | JCDabstract_domain x -> JCDabstract_domain x
    | JCDannotation_policy x -> JCDannotation_policy x
    | JCDseparation_policy x -> JCDseparation_policy x
    | JCDinvariant_policy x -> JCDinvariant_policy x
    | JCDaxiomatic(id,l) -> JCDaxiomatic(id,List.map decl l)
  in new decl ~pos:d#pos dnode
	  
let decls dlist =
  let unit_type = new ptype (JCPTnative Tunit) in
  [
    new decl (JCDexception(name_for_loop_exit,Some unit_type));
    new decl (JCDexception(name_for_loop_continue,Some unit_type));
    new decl (JCDexception(name_for_return_label,Some unit_type));
  ]
  @ Hashtbl.fold (fun _ exc acc ->
		    new decl (JCDexception(exc#name,Some unit_type))
		    :: acc
		 ) label_to_exception []
  @ List.map decl dlist

(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)
