(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: output.ml,v 1.24 2004-12-07 17:19:24 hubert Exp $ i*)

open Format;;

type constant =
  | Prim_int of int64
  | Prim_float of string
  | Prim_bool of bool
;;

let fprintf_constant form e =
  match e with
    | Prim_int(n) when Int64.compare n Int64.zero < 0 -> fprintf form "(%Ld)" n
    | Prim_int(n) -> fprintf form "%Ld" n
    | Prim_float(f) -> fprintf form "%s" f
    | Prim_bool(b) -> fprintf form "%b" b
;;

type term = 
  | LConst of constant
  | LApp of string * term list
  | LVar of string
  | LVarAtLabel of string * string     (*r x@L *)
;;

let rec iter_term f t =
  match t with
  | LConst(c) -> ()
  | LApp(id,l) -> f id; List.iter (iter_term f) l
  | LVar(id) -> f id
  | LVarAtLabel(id,l) -> f id
;;

let rec fprintf_term form t =
  match t with
  | LConst(c) -> fprintf_constant form c
  | LApp("eq_pointer",[t1;t2]) ->
      fprintf form "@[(%a=%a)@]" 
	fprintf_term t1
	fprintf_term t2
  | LApp("ne_pointer",[t1;t2]) ->
      fprintf form "@[neqv(%a,%a)@]" 
	fprintf_term t1
	fprintf_term t2
  | LApp(id,t::tl) ->
      fprintf form "@[%s(%a" id fprintf_term t;
      List.iter (fun t -> fprintf form ",@ %a" fprintf_term t) tl;
      fprintf form ")@]"
  | LApp(id,[])
  | LVar(id) -> fprintf form "%s" id
  | LVarAtLabel(id,l) -> fprintf form "%s@@%s" id l
;;

type base_type = string list * string       (*r int, float, int list, ... *)

type assertion = 
  | LTrue | LFalse
  | LAnd of assertion * assertion
  | LOr of assertion * assertion
  | LIff of assertion * assertion
  | LNot of assertion
  | LImpl of assertion * assertion
  | LIf of term * assertion * assertion
  | LLet of string * term * assertion
      (*r warning: only for Coq assertions *)
  | LForall of string * base_type * assertion
      (*r forall x:t.a *)
  | LExists of string * base_type * assertion
      (*r exists x:t.a *)
  | LPred of string * term list
  | LNamed of string * assertion
;;

let make_or a1 a2 =
  match (a1,a2) with
    | (LTrue,_) -> LTrue
    | (_,LTrue) -> LTrue
    | (LFalse,_) -> a2
    | (_,LFalse) -> a1
    | (_,_) -> LOr(a1,a2)

let make_and a1 a2 =
  match (a1,a2) with
    | (LTrue,_) -> a2
    | (_,LTrue) -> a1
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
    | (_,_) -> LAnd(a1,a2)

let rec make_and_list l =
  match l with
    | [] -> LTrue
    | f::r -> make_and f (make_and_list r)

let make_impl a1 a2 =
  match (a1,a2) with
    | (LTrue,_) -> a2
    | (_,LTrue) -> LTrue
    | (LFalse,_) -> LTrue
    | (_,LFalse) -> LNot(a1)
    | (_,_) -> LImpl(a1,a2)

let make_equiv a1 a2 =
  match (a1,a2) with
    | (LTrue,_) -> a2
    | (_,LTrue) -> a1
    | (_,_) -> LIff(a1,a2)

let rec iter_assertion f a =
  match a with
  | LTrue -> ()
  | LFalse -> () 
  | LAnd(a1,a2) -> iter_assertion f a1; iter_assertion f a2 
  | LOr(a1,a2) -> iter_assertion f a1; iter_assertion f a2 
  | LIff(a1,a2) -> iter_assertion f a1; iter_assertion f a2 
  | LNot(a1) -> iter_assertion f a1
  | LImpl(a1,a2) -> iter_assertion f a1; iter_assertion f a2 
  | LIf(t,a1,a2) -> 
      iter_term f t; iter_assertion f a1; iter_assertion f a2 
  | LLet(id,t,a) -> iter_term f t; iter_assertion f a
  | LForall(id,(l,t),a) -> List.iter f l;f t; iter_assertion f a
  | LExists(id,(l,t),a) -> List.iter f l;f t; iter_assertion f a
  | LPred(id,l) -> f id; List.iter (iter_term f) l
  | LNamed (_, a) -> iter_assertion f a
;;

let fprintf_base_type form (l,t) =
  match l with
    | [] -> fprintf form "%s" t
    | [x] ->
	fprintf form "%s %s" x t
    | x::l ->
	fprintf form "(%s" x;
	List.iter (fun t -> fprintf form ",%s" t) l;
	fprintf form ") %s" t

let rec fprintf_assertion form a =
  match a with
  | LTrue -> fprintf form "true"
  | LFalse -> fprintf form "false"
  | LAnd(a1,a2) -> 
      fprintf form "@[(%a@ and %a)@]" 
	fprintf_assertion a1 
	fprintf_assertion a2
  | LOr(a1,a2) -> 
      fprintf form "@[(%a@ or %a)@]" 
	fprintf_assertion a1 
	fprintf_assertion a2
  | LIff(a1,a2) -> 
      fprintf form "@[(%a@ <-> %a)@]" 
	fprintf_assertion a1 
	fprintf_assertion a2
  | LNot(a1) -> 
      fprintf form "@[(not %a)@]" 
	fprintf_assertion a1
  | LImpl(a1,a2) -> 
      fprintf form "@[<hv 1>(%a ->@ %a)@]" 
	fprintf_assertion a1 fprintf_assertion a2
  | LIf(t,a1,a2) -> 
      fprintf form "@[<hv 1>(if %a@ then %a@ else %a)@]" 
	fprintf_term t fprintf_assertion a1 fprintf_assertion a2
  | LLet(id,t,a) -> 
      fprintf form "@[<hv 1>(let @[<hv 1>%s =@ %a in@]@ %a)@]" id
	fprintf_term t fprintf_assertion a
  | LForall(id,t,a) -> 
      fprintf form "@[<hv 1>(forall %s:%a.@ %a)@]" 
	id fprintf_base_type t fprintf_assertion a
  | LExists(id,t,a) -> 
      fprintf form "@[<hv 1>(exists %s:%a.@ %a)@]" 
	id fprintf_base_type t fprintf_assertion a
  | LPred("eq",[t1;t2]) ->
      fprintf form "@[(%a = %a)@]" 
	fprintf_term t1
	fprintf_term t2
  | LPred("neq",[t1;t2]) ->
      fprintf form "@[(%a <> %a)@]" 
	fprintf_term t1
	fprintf_term t2
  | LPred(id,t::tl) ->
      fprintf form "@[%s(%a" id fprintf_term t;
      List.iter (fun t -> fprintf form ",@ %a" fprintf_term t) tl;
      fprintf form ")@]"
  | LPred(_,_) -> assert false      
  | LNamed (n, a) ->
      fprintf form "@[(:%s:@ %a)@]" n fprintf_assertion a
;;

(*s types *)


type why_type = 
  | Prod_type of string * why_type * why_type      (*r (x:t1)->t2 *)
  | Base_type of base_type
  | Ref_type of why_type
  | Annot_type of 
      assertion * why_type * 
      string list * string list * assertion * ((string * assertion) option)
	(*r { P } t reads r writes w { Q | E => R } *)
;;

let base_type s = Base_type([],s);;
let int_type = base_type "int";;
let bool_type = base_type "bool";;
let float_type = base_type "real";;
let unit_type = base_type "unit";;

let option_iter f x =
  match x with
    | None -> ()
    | Some y -> f y
;;

let rec iter_base_type f (tl,id) = List.iter f tl; f id

let rec iter_why_type f t =
  match t with
    | Prod_type(_,t1,t2) ->
	iter_why_type f t1; iter_why_type f t2
    | Base_type b -> iter_base_type f b
    | Ref_type(t) -> iter_why_type f t 
    | Annot_type (pre,t,reads,writes,post,signals) ->
	iter_assertion f pre;
	iter_why_type f t;
	List.iter f reads;
	List.iter f writes;
	iter_assertion f post;
	option_iter (fun (_,a) -> iter_assertion f a) signals
;;


let rec fprint_comma_string_list form l =
  match l with
    | [] -> ()
    | x::l -> 
	fprintf form ",%s" x;
	fprint_comma_string_list form l
;;

let rec fprintf_type anon form t = 
  match t with
    | Prod_type(id,t1,t2) ->
	if id="" or anon then
	  fprintf form "@[<hv 1>%a ->@ %a@]" 
	    (fprintf_type anon) t1 (fprintf_type anon) t2
	else
	  fprintf form "@[<hv 1>%s:%a ->@ %a@]" id
	    (fprintf_type anon) t1 (fprintf_type anon) t2
    | Base_type t  -> 
	fprintf_base_type form t
    | Ref_type(t) -> 
	fprintf form "%a ref" (fprintf_type anon) t
    | Annot_type(p,t,reads,writes,q,signals) ->
	begin
	  fprintf form "@[@[<hv 2>{ "; 
	  if p <> LTrue 
	  then fprintf_assertion form p;
	  fprintf form "}@]@ %a@ " (fprintf_type anon) t;
	  begin
	    match List.sort compare reads with
	      | [] -> ()
	      | r::l -> 
		  fprintf form "reads %s%a@ " r fprint_comma_string_list l
	  end;
	  begin
	    match List.sort compare writes with
	      | [] -> ()
	      | r::l -> 
		  fprintf form "writes %s%a@ " r fprint_comma_string_list l
	  end;
	  begin
	    match signals with
	      | None -> 
		  fprintf form "@[<hv 2>{ %a }@]@]" fprintf_assertion q
	      | Some(e,r) ->
		  fprintf form 
		    "raises %s@ @[<hv 2>{ %a@ | @[<hv 2>%s =>@ %a@] }@]@]" 
		    e
		    fprintf_assertion q
		    e 
		    fprintf_assertion r
	  end		    
	  
	end
;;

let fprint_base_type form b =
  match b with
    | ([],s) -> fprintf form "-> %s" s
    | (t::tl,s) -> 
	fprintf form "-> (%s" t;
	List.iter (fun t -> fprintf form ",%s" t) tl;
	fprintf form ") %s" s 

let rec fprint_logic_type sep form t = 
  match t with
    | Prod_type(_,Base_type([],s),t2) ->
	fprintf form "@[<hv 1>%s%s%a@]" sep s (fprint_logic_type ", ") t2
    | Prod_type(_,Base_type(t::tl,s),t2) ->
	fprintf form "@[<hv 1>%s(%s" sep t;
	List.iter (fun t -> fprintf form ",%s" t) tl;
	fprintf form ") %s %a@]" s (fprint_logic_type ", ") t2
    | Base_type b -> fprint_base_type form b 
    | Ref_type(_) -> assert false (* should never happen *)
    | Prod_type _ -> assert false (* should never happen *)
    | Annot_type _ -> assert false (* should never happen *)
;;

let fprint_logic_type = fprint_logic_type ""

(*s expressions *)

type variant = term * string option

type expr =
  | Cte of constant
  | Var of string
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Void
  | Deref of string
  | If of expr * expr * expr
  | While of 
      expr (* loop condition *)
      * assertion (* invariant *) 
      * variant (* variant *) 
      * expr list (* loop body *)
  | Block of expr list
  | Assign of string * expr
  | Let of string * expr * expr
  | Let_ref of string * expr * expr
  | App of expr * expr
  | Raise of string * expr option
  | Try of expr * string * string option * expr
  | Fun of (string * why_type) list * 
      assertion * expr * assertion * ((string * assertion) option)
  | Triple of assertion * expr * assertion * ((string * assertion) option)
  | Assert of assertion  (*r only in blocks *)
  | Label of string
  | BlackBox of why_type
;;

let make_or_expr a1 a2 =
  match (a1,a2) with
    | (Cte (Prim_bool true),_) -> Cte (Prim_bool true)
    | (_,Cte (Prim_bool true)) -> Cte (Prim_bool true)
    | (Cte (Prim_bool false),_) -> a2
    | (_,Cte (Prim_bool false)) -> a1
    | (_,_) -> Or(a1,a2)

let make_and_expr a1 a2 =
  match (a1,a2) with
    | (Cte (Prim_bool true),_) -> a2
    | (_,Cte (Prim_bool true)) -> a1
    | (Cte (Prim_bool false),_) -> Cte (Prim_bool false)
    | (_,Cte (Prim_bool false)) ->Cte (Prim_bool false)
    | (_,_) -> And(a1,a2)


let rec make_app_rec accu l =
  match l with
    | [] -> accu
    | e::r -> make_app_rec (App(accu,e)) r
;;

let make_app id l = make_app_rec (Var(id)) l

let make_while cond inv var e =
  let body = 
    match e with
      | Block(l) -> l
      | _ -> [e]
  in While(cond,inv,var,body)
;;

let make_label label e =
  let body = 
    match e with
      | Block(l) -> l
      | _ -> [e]
  in Block(Label label::body)
;;

let make_pre pre e =  Triple(pre,e,LTrue,None)

let append e1 e2 =
  match e1,e2 with
    | Void,_ -> e2
    | _,Void -> e1
    | Block(l1),Block(l2) -> Block(l1@l2)
    | Block(l1),_ -> Block(l1@[e2])
    | _,Block(l2) -> Block(e1::l2)
    | _ -> Block [e1;e2]
;;

let rec iter_expr f e =
  match e with
    | Cte(c) -> ()
    | Var(id) -> f id
    | And(e1,e2) -> iter_expr f e1; iter_expr f e2
    | Or(e1,e2) -> iter_expr f e1; iter_expr f e2
    | Not(e1) -> iter_expr f e1
    | Void -> ()
    | Deref(id) -> f id
    | If(e1,e2,e3) ->
	iter_expr f e1; iter_expr f e2; iter_expr f e3
    | While(e1,inv,(var,_),e2) ->
	iter_expr f e1; 
	iter_assertion f inv; 
	iter_term f var; 
	List.iter (iter_expr f) e2
    | Block(el) -> List.iter (iter_expr f) el
    | Assign(id,e) -> f id; iter_expr f e
    | Let(id,e1,e2) -> iter_expr f e1; iter_expr f e2
    | Let_ref(id,e1,e2) -> iter_expr f e1; iter_expr f e2
    | App(e1,e2) -> iter_expr f e1; iter_expr f e2
    | Raise (_, None) -> ()
    | Raise(id,Some e) -> iter_expr f e
    | Try(e1,exc,id,e2) -> iter_expr f e1; iter_expr f e2
    | Fun(params,pre,body,post,signals) ->
	iter_assertion f pre;
	iter_expr f body;
	iter_assertion f post;
	option_iter (fun (_,a) -> iter_assertion f a) signals
    | Triple(pre,e,post,exceps) ->
	iter_assertion f pre;
	iter_expr f e;
	iter_assertion f post;
	option_iter (fun (_,a) -> iter_assertion f a) exceps
    | Assert(e) -> iter_assertion f e
    | Label s -> ()
    | BlackBox(ty) -> iter_why_type f ty


let fprintf_variant form = function
  | t, None -> fprintf_term form t
  | t, Some r -> fprintf form "%a for %s" fprintf_term t r
	  
let rec fprintf_expr form e =
  match e with
    | Cte(c) -> fprintf_constant form c
    | Var(id) -> fprintf form "%s" id
    | And(e1,e2) ->
	fprintf form "@[(%a && %a)@]" 
	  fprintf_expr e1 fprintf_expr e2
    | Or(e1,e2) ->
	fprintf form "@[(%a || %a)@]" 
	  fprintf_expr e1 fprintf_expr e2
    | Not(e1) ->
	fprintf form "@[(not %a)@]" 
	  fprintf_expr e1 
    | Void -> fprintf form "void"
    | Deref(id) -> fprintf form "!%s" id
    | If(e1,e2,e3) ->
	fprintf form "@[<hv 0>if %a@ @[<hv 1>then@ %a@]@ @[<hv 1>else@ %a@]@]" 
	  fprintf_expr e1 fprintf_expr e2 fprintf_expr e3
    | While(e1,inv,var,e2) ->
	fprintf form 
	  "@[<hv 0>while %a do@ @[<hv 1>@[<hv 2>{ @[<hv 2>invariant@ %a@]@ @[<hv 2>variant@ %a@] }@]@ %a@]@ done@]" 
	  fprintf_expr e1 
	  fprintf_assertion inv
	  fprintf_variant var
	  fprintf_expr_list e2
    | Block([]) ->
	fprintf form "void"
    | Block(el) ->
	fprintf form "@[<hv 0>begin@ @[<hv 1>  %a@]@ end@]" fprintf_expr_list el
    | Assign(id,e) ->
	fprintf form "@[<hv 1>%s := %a@]" 
	  id fprintf_expr e
    | Let(id,e1,e2) ->
	fprintf form "@[<hv 0>let %s = %a in@ %a@]" id
	  fprintf_expr e1 fprintf_expr e2
    | Let_ref(id,e1,e2) ->
	fprintf form "@[<hv 0>let %s = ref %a in@ %a@]" id
	  fprintf_expr e1 fprintf_expr e2
    | App(e1,e2) ->
	fprintf form "@[<hv 1>(%a %a)@]" fprintf_expr e1 fprintf_expr e2
    | Raise(id,None) ->
	fprintf form "@[<hv 1>raise@ %s@]" id
    | Raise(id,Some e) ->
	fprintf form "@[<hv 1>raise@ (%s@ %a)@]" id fprintf_expr e
    | Try(e1,exc,None,e2) ->
	fprintf form "@[<hv 1>try@ %a@ with@ %s ->@ %a end@]" 
	  fprintf_expr e1 exc fprintf_expr e2
    | Try(e1,exc,Some id,e2) ->
	fprintf form "@[<hv 1>try@ %a@ with@ %s %s ->@ %a end@]" 
	  fprintf_expr e1 exc id fprintf_expr e2
    | Fun(params,pre,body,post,signals) ->
	fprintf form "@[<hv 1>fun @[";
	List.iter 
	  (fun (x,t) -> fprintf form "(%s : %a) " x (fprintf_type false) t) 
	  params;
	fprintf form "@]->@ @[<hv 0>{ "; 
	if pre <> LTrue 
	then fprintf_assertion form pre;
	fprintf form " }@ %a@]@ " fprintf_expr body;
	begin
	  match signals with
	    | None -> 
		fprintf form "@[<hv 2>{ %a }@]@]" fprintf_assertion post
	    | Some(e,r) ->
		fprintf form 
		  "@[<hv 2>{ %a@ | @[<hv 2>%s =>@ %a@] }@]@]" 
		  fprintf_assertion post
		  e 
		  fprintf_assertion r
	end		    

    | Triple(pre,e,LTrue,None) ->
	fprintf form "@[<hv 0>{ %a }@ (%a)@ { }@]" 
	  fprintf_assertion pre
	  fprintf_expr e
    | Triple(pre,e,post,exceps) ->
	fprintf form "@[<hv 0>{ %a }@ (%a)@ " 
	  fprintf_assertion pre
	  fprintf_expr e;
	begin
	  match exceps with
	    | None -> 
		fprintf form "{ %a }@]" 
		  fprintf_assertion post
	    | Some(e,r) ->
		fprintf form 
		  "@[<hv 2>{ %a@ | @[<hv 2>%s =>@ %a@] }@]@]" 
		  fprintf_assertion post
		  e 
		  fprintf_assertion r
	end
    | Assert(e) ->
	fprintf form "@[<hv 0>assert@ { %a }@]" 
	  fprintf_assertion e
    | Label s ->
	fprintf form "@[<hv 0>label@ %s@]" s
    | BlackBox(t) ->
	fprintf form "@[<hv 0>[ %a ]@]" 
	  (fprintf_type false) t

	  

and fprintf_expr_list form l =
  match l with
    | [] -> ()
    | e::l ->
	fprintf form "%a" fprintf_expr e;
	fprintf_expr_end_list form l

and fprintf_expr_end_list form l =
  match l with
    | [] -> ()
    | e::l ->
	fprintf form ";@ %a" fprintf_expr e;
	fprintf_expr_end_list form l
;;

type why_decl =
  | Param of bool * string * why_type         (*r parameter in why *)
  | Def of string * expr               (*r global let in why *)
  | Logic of bool * string * why_type         (*r logic decl in why *)
  | Axiom of string * assertion         (*r Axiom *)
  | Predicate of bool * string * (string * base_type) list * assertion  

type prover_decl =
  | Parameter  of string * why_type    (*r Parameter *)
  | Definition of string * expr        (*r Definition *) 
(*
  | Predicate of string * (string * why_type) list * assertion  (*r Predicate *) 
*)
  | CoqVerbatim of string                 (*r Text in Coq *)


let get_why_id d =
  match d with
    | Param(_,id,_) -> id
    | Logic(_,id,_) -> id
    | Def(id,_) -> id
    | Axiom(id,_) -> id
    | Predicate(_,id,_,_) -> id
      
let iter_why_decl f d =
  match d with
    | Param(_,_,t) -> iter_why_type f t
    | Logic(_,id,t) -> iter_why_type f t
    | Def(id,t) -> iter_expr f t
    | Axiom(id,t) -> iter_assertion f t
    | Predicate(_,id,args,p) -> 
	List.iter (fun (_,t) -> iter_base_type f t) args;
	iter_assertion f p
    
let get_prover_id d =
  match d with
    | Parameter(id,_) -> id
(*
    | Axiom(id,_) -> id
*)
    | Definition(id,_) -> id
(*
    | Predicate(id,_,_) -> id
*)
    | CoqVerbatim(s) -> assert false


type state = [`TODO | `RUNNING | `DONE ];;

type 'a decl = { mutable state : state; decl : 'a };;

module StringMap = Map.Make(String);;

(*
exception Recursion;;
*)

let rec do_topo decl_map iter_fun output_fun d =
  match d.state with
    | `DONE -> ()
    | `RUNNING -> 
	Creport.warning Loc.dummy "Recursive definition in generated file"
    | `TODO ->
	d.state <- `RUNNING;
	iter_fun
	  (fun id ->
	     try 
	       let s = StringMap.find id decl_map in
	       do_topo decl_map iter_fun output_fun s
	     with
		 Not_found -> ())
	  d.decl;	
	output_fun d.decl;
	d.state <- `DONE
;;


let build_map get_id decl_list =
  List.fold_left
    (fun acc decl ->
       let id = get_id decl in
       StringMap.add id { state = `TODO ; decl = decl } acc)
    StringMap.empty
    decl_list
;;

let fprint_logic_arg form (id,t) =
  fprintf form "%s:%a" id fprintf_base_type t

let fprintf_why_decl form d =
  match d with
    | Param(b,id,t) ->
	fprintf form "@[<hv 1>%sparameter %s :@ %a@]@.@." 
	(if b then "external" else "") id 
	  (fprintf_type false) t
    | Logic(b,id,t) ->
	fprintf form "@[<hv 1>%slogic %s :@ %a@]@.@." 
	(if b then "external" else "") id 
	  fprint_logic_type t
    | Axiom(id,p) ->
	fprintf form "@[<hv 1>axiom %s :@ %a@]@.@." id 
	  fprintf_assertion p
    | Def(id,e) ->
	fprintf form "@[<hv 1>let %s =@ %a@]@.@." id fprintf_expr e
    | Predicate(b,id,[],p) -> assert false
    | Predicate(b,id,a::args,p) ->
	fprintf form "@[<hv 1>%spredicate %s(%a"
	  (if b then "external" else "") id 
	  fprint_logic_arg a;
	List.iter (fun a -> fprintf form ",%a" fprint_logic_arg a) args;
	fprintf form ") =@ %a@]@.@." fprintf_assertion p


let iter_prover_decl f d =
  match d with
    | Parameter(id,t) -> iter_why_type f t
(*
    | Axiom(id,t) -> iter_assertion f t
*)
    | Definition(id,e) -> iter_expr f e
(*
    | Predicate(id,args,a) -> iter_assertion f a
*)
    | CoqVerbatim (s) -> assert false

(*
let fprint_coq_decl form d =
  match d with
    | Parameter(id,t) -> 
	fprintf form "@[<hv 1>Parameter %s :@ %a.@]@.@." id 
	  (fprint_coq_type true) t
    | Axiom(id,t) -> 
	fprintf form "@[<hv 1>Axiom %s :@ %a.@]@.@." id 
	  (fprint_coq_type false) t
    | Definition(id,e) ->
	fprintf form "@[<hv 1>Definition %s :=@ %a.@]@.@." id fprintf_expr e
    | Predicate(id,args,a) ->
	fprintf form "@[<hv 1>Definition %s := fun@ " id;
	List.iter 
	  (fun (x,t) -> fprintf form "(%s : %a)@ " x (fprint_coq_type true) t) 
	  args;
	fprintf form "=> %a.@]@.@." (fprint_assertion true) a
    | Verbatim (s) -> fprintf form "%s@." s
*)

let output_decls get_id iter_decl output_decl decls =
  let map = build_map get_id decls in
  StringMap.iter
    (fun id decl ->
       do_topo map iter_decl output_decl decl)
    map
;;

let fprintf_why_decls form decls =
  (* Why do we need a partition ?
     because one may have a logic and a parameter with the same name, 
     and the computation of dependencies is confused in that case

     Logic may not depend on anything
     Predicate may depend on other Predicate and Logic
     Axiom may depend on Predicate and Logic
     Parameter may depend on Predicate and Logic
     Def may depend on Predicate, Logic, Parameter and Def

     - Claude, 03 apr 2004
  *)
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) decls;
(***
  let (logic,other) = 
    List.partition
      (function Logic _ | Predicate _ -> true | _ -> false) 
      decls
  in
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) logic;
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) other
***)
;;

(*
let output_coq_decls form decls =
  let (coqdef,other) =
    List.partition
      (function CoqVerbatim _ -> false 
	 | _ -> true) 
      decls
  in
  output_decls get_coq_id iter_coq_decl (fprint_coq_decl form) coqdef;
  List.iter (fprint_coq_decl form) other;
;;
*)








