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

(*i $Id: util.ml,v 1.96 2004-07-08 07:12:29 filliatr Exp $ i*)

open Logic
open Ident
open Misc
open Types
open Ast
open Env
open Rename
open Cc

(*s References mentioned by a predicate *)

let is_reference env id =
  (is_in_env env id) && (is_mutable (type_in_env env id))

let predicate_now_refs env c =
  Idset.filter (is_reference env) (predicate_vars c)

let term_now_refs env c =
  Idset.filter (is_reference env) (term_vars c)


let labelled_reference env id =
  if is_reference env id then
    id
  else if is_at id then
    let uid,_ = Ident.un_at id in 
    if is_reference env uid then uid else failwith "caught"
  else
    failwith "caught"

let set_map_succeed f s = 
  Idset.fold 
    (fun x e -> try Idset.add (f x) e with Failure _ -> e) 
    s Idset.empty

let predicate_refs env c =
  set_map_succeed (labelled_reference env) (predicate_vars c)

let term_refs env c =
  set_map_succeed (labelled_reference env) (term_vars c)

let post_refs env q =
  set_map_succeed (labelled_reference env) (post_vars q)

(*s Labels management *)

let gen_change_label f c =
  let ids = Idset.elements (predicate_vars c) in
  let s = 
    List.fold_left 
      (fun s id -> 
	 if is_at id then 
	   try Idmap.add id (f (un_at id)) s with Failure _ -> s
	 else s)
      Idmap.empty ids
  in
  subst_in_predicate s c

let erase_label l c =
  gen_change_label 
    (function (uid,l') when l = l' -> uid | _ -> failwith "caught") c

let change_label l1 l2 c =
  gen_change_label 
    (function (uid,l) when l = l1 -> at_id uid l2 | _ -> failwith "caught") c

let put_label_term env l t =
  let ids = term_refs env t in
  let s = 
    Idset.fold (fun id s -> Idmap.add id (at_id id l) s) ids Idmap.empty 
  in
  subst_in_term s t

let put_label_predicate env l p =
  let ids = predicate_refs env p in
  let s = 
    Idset.fold (fun id s -> Idmap.add id (at_id id l) s) ids Idmap.empty 
  in
  subst_in_predicate s p

let oldify env ef t =
  let ids = term_refs env t in
  let s =
    Idset.fold 
      (fun id s -> 
	 if Effect.is_write ef id then Idmap.add id (at_id id "") s else s)
      ids Idmap.empty
  in
  subst_in_term s t

let type_c_subst_oldify env x t k =
  let s = subst_one x t in 
  let s_old = subst_one x (oldify env k.c_effect t) in
  { c_result_name = k.c_result_name;
    c_result_type = type_v_rsubst s k.c_result_type;
    c_effect = k.c_effect;
    c_pre = List.map (asst_app (tsubst_in_predicate s)) k.c_pre;
    c_post = option_app (post_app (tsubst_in_predicate s_old)) k.c_post }

(*s shortcuts for typing information *)

let effect p = p.info.kappa.c_effect
let obligations p = p.info.obligations
let pre p = p.info.kappa.c_pre
let preo p = pre p @ obligations p
let post p = p.info.kappa.c_post
let result_type p = p.info.kappa.c_result_type
let result_name p = p.kappa.c_result_name

let erase_exns ti = 
  let k = ti.kappa in
  { ti with kappa = { k with c_effect = Effect.erase_exns k.c_effect } }

(*s [apply_pre] and [apply_post] instantiate pre- and post- conditions
    according to a given renaming of variables (and a date that means
    `before' in the case of the post-condition). *)

let make_subst before ren env ids =
  Idset.fold
    (fun id s ->
       if is_reference env id then
	 Idmap.add id (current_var ren id) s
       else if is_at id then
	 let uid,d = un_at id in
	 if is_reference env uid then begin
	   let d' = match d, before with
	     | "", None -> assert false
	     | "", Some l -> l
	     | _ -> d
	   in
	   Idmap.add id (var_at_date ren d' uid) s
	 end else
	   s
       else
	 s) 
    ids Idmap.empty

let apply_term ren env t =
  let ids = term_vars t in
  let s = make_subst None ren env ids in
  subst_in_term s t

let apply_assert ren env c =
  let ids = predicate_vars c.a_value in
  let s = make_subst None ren env ids in
  { c with a_value = subst_in_predicate s c.a_value }
 
let apply_post before ren env q =
  let ids = post_vars q in
  let s = make_subst (Some before) ren env ids in
  post_app (subst_in_predicate s) q
  
(*s [traverse_binder ren env bl] updates renaming [ren] and environment [env]
    as we cross the binders [bl]. *)

let rec traverse_binders env = function
  | [] -> 
      env
  | (id, BindType v) :: rem ->
      traverse_binders (Env.add id v env) rem
  | (id, BindSet) :: rem ->
      traverse_binders (Env.add_set id env) rem
  | (_, Untyped) :: _ ->
      invalid_arg "traverse_binders"
	  
let initial_renaming env =
  let ids = Env.fold_all (fun (id,_) l -> id::l) env [] in
  update empty_ren "%init" ids


(*s Occurrences *)

let rec occur_term id = function
  | Tvar id' | Tderef id' -> id = id'
  | Tapp (_, l) -> List.exists (occur_term id) l
  | Tconst _ -> false

let rec occur_predicate id = function
  | Pvar _ | Ptrue | Pfalse -> false
  | Papp (_, l) -> List.exists (occur_term id) l
  | Pif (a, b, c) -> 
      occur_term id a || occur_predicate id b || occur_predicate id c
  | Forallb (_, _, _, _, a, b) 
  | Pimplies (_, a, b) 
  | Pand (_, a, b) 
  | Piff (a, b) 
  | Por (a, b) -> occur_predicate id a || occur_predicate id b
  | Pnot a -> occur_predicate id a
  | Forall (_,_,_,_,a) -> occur_predicate id a
  | Exists (_,_,_,a) -> occur_predicate id a
  | Pfpi (t,_,_) -> occur_term id t

let occur_assertion id a = occur_predicate id a.a_value

let occur_post id = function 
  | None -> 
      false 
  | Some (q,l) -> 
      occur_assertion id q || 
      List.exists (fun (_,a) -> occur_assertion id a) l

let rec occur_type_v id = function
  | Ref v -> occur_type_v id v
  | Array v -> occur_type_v id v
  | Arrow (bl, c) -> occur_arrow id bl c
  | PureType _ -> false

and occur_type_c id c =
  occur_type_v id c.c_result_type ||
  List.exists (occur_assertion id) c.c_pre ||
  Effect.occur id c.c_effect ||
  occur_post id c.c_post 

and occur_arrow id bl c = match bl with
  | [] -> 
      occur_type_c id c
  | (id', BindType v) :: bl' -> 
      occur_type_v id v || (id <> id' && occur_arrow id bl' c)
  | (_, (BindSet | Untyped)) :: bl' -> 
      occur_arrow id bl' c

let forall ?(is_wp=false) x v p = match v with
  (* particular case: $\forall b:bool. Q(b) = Q(true) and Q(false)$ *)
  | PureType PTbool ->
      let ptrue = tsubst_in_predicate (subst_one x ttrue) p in
      let pfalse = tsubst_in_predicate (subst_one x tfalse) p in
      let n = Ident.bound x in
      let p = subst_in_predicate (subst_onev x n) p in
      Forallb (is_wp, x, n, p, simplify ptrue, simplify pfalse)
  | _ ->
      let n = Ident.bound x in
      let p = subst_in_predicate (subst_onev x n) p in
      Forall (is_wp, x, n, mlize_type v, p)

let foralls ?(is_wp=false) =
  List.fold_right
    (fun (x,v) p -> if occur_predicate x p then forall ~is_wp x v p else p)
    
let pforall ?(is_wp=false) x v p =
  if p = Ptrue then Ptrue else forall ~is_wp x v p

let exists x v p =
  let n = Ident.bound x in
  let p = subst_in_predicate (subst_onev x n) p in
  Exists (x, n, mlize_type v, p)

let pexists x v p = 
  if p = Ptrue then Ptrue else exists x v p

let exists x v p = 
  let n = Ident.bound x in
  let p = subst_in_predicate (subst_onev x n) p in
  Exists (x, n, mlize_type v, p)

(* misc. functions *)

let deref_type = function
  | Ref v -> v
  | _ -> invalid_arg "deref_type"

let dearray_type = function
  | Array v -> v
  | _ -> invalid_arg "dearray_type"

let decomp_kappa c = 
  ((c.c_result_name, c.c_result_type), c.c_effect, c.c_pre, c.c_post)

let id_from_name = function Name id -> id | Anonymous -> (Ident.create "X")

(* [decomp_boolean c] returns the specs R and S of a boolean expression *)

let equality t1 t2 = Papp (t_eq, [t1; t2])

let tequality v t1 t2 = match v with
  | PureType PTint -> Papp (t_eq_int, [t1; t2])
  | PureType PTbool -> Papp (t_eq_bool, [t1; t2])
  | PureType PTreal -> Papp (t_eq_real, [t1; t2])
  | PureType PTunit -> Papp (t_eq_unit, [t1; t2])
  | _ -> Papp (t_eq, [t1; t2])

let decomp_boolean ({ a_value = c }, _) =
  (* q -> if result then q(true) else q(false) *)
  let ctrue = tsubst_in_predicate (subst_one Ident.result ttrue) c in
  let cfalse = tsubst_in_predicate (subst_one Ident.result tfalse) c in
  simplify ctrue, simplify cfalse

(*s [make_access env id c] Access in array id.
    Constructs [t:(array s T)](access_g s T t c ?::(lt c s)). *)

let array_info env id =
  let ty = type_in_env env id in
  let v = dearray_type ty in
  (*i let ty_elem = trad_ml_type_v ren env v in
  let ty_array = trad_imp_type ren env ty in i*)
  v

let make_raw_access env (id,id') c =
  let _ = array_info env id in
  Tapp (Ident.access, [Tvar id'; c])

let make_pre_access env id c =
  let _ = array_info env id in
  let c = unref_term c in
  Pand (false, le_int (Tconst (ConstInt 0)) c, lt_int c (array_length id))
      
let make_raw_store env (id,id') c1 c2 =
  let _ = array_info env id in
  Tapp (Ident.store, [Tvar id'; c1; c2])

(*s to build AST *)

let make_lnode loc p env o k = 
  { desc = p; 
    info = { loc = loc; env = env; label = label_name (); 
	     obligations = o; kappa = k } }

let make_var loc x t env =
  make_lnode loc (Expression (Tvar x)) env [] (type_c_of_v t)

let make_expression loc e t env =
  make_lnode loc (Expression e) env [] (type_c_of_v t)
    
let make_bool loc b env = 
  make_expression loc (Tconst (ConstBool b)) (PureType PTbool) env

let make_annot_bool loc b env =
  let e = make_bool loc b env in
  let k = type_c_of_v (PureType PTbool) in
  let b = Tconst (ConstBool b) in
  let q = anonymous loc (equality (Tvar result) b) in
  make_lnode loc (Expression b) env [] { k with c_post = Some (q, []) }

let make_void loc env = 
  make_expression loc (Tconst ConstUnit) (PureType PTunit) env 

let make_raise loc x v env =
  let k = type_c_of_v v in
  let ef = Effect.add_exn exit_exn Effect.bottom in
  make_lnode loc (Raise (x, None)) env [] { k with c_effect = ef }

(*s Pretty printers (for debugging purposes) *)

open Format
open Pp

let print_pre fmt l = 
  if l <> [] then begin
    fprintf fmt "@[ ";
    print_list semi (fun fmt p -> print_predicate fmt p.a_value) fmt l;
    fprintf fmt " @]"
  end

let print_assertion fmt a = print_predicate fmt a.a_value

let print_exn fmt (x,c) = 
  fprintf fmt "| %a => @[%a@]@," Ident.print x print_assertion c

let print_post fmt = function
  | None -> 
      ()
  | Some (c,[]) -> 
      fprintf fmt "@[ %a @]" print_assertion c
  | Some (c, l) -> 
      fprintf fmt "@[ %a@ %a @]" print_assertion c 
	(print_list space print_exn) l

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTreal -> fprintf fmt "real"
  | PTarray t -> fprintf fmt "(%a array)" print_pure_type t
  | PTexternal([],id) -> fprintf fmt "%a" Ident.print id
  | PTvarid(id) -> fprintf fmt "'%a" Ident.print id
  | PTvar(v) -> fprintf fmt "'a%d" v.tag
  | PTexternal([t],id) -> fprintf fmt "(%a %a)" print_pure_type t Ident.print id
  | PTexternal(l,id) -> fprintf fmt "((%a) %a)" 
      (print_list space print_pure_type) l
      Ident.print id

and print_type_v fmt = function
  | Arrow (b,c) ->
      fprintf fmt "@[<hov 2>%a ->@ %a@]" 
	(print_list arrow pp_binder) b print_type_c c
  | v -> 
      print_type_v2 fmt v

and pp_binder fmt = function
  | id, BindType v when id == Ident.anonymous -> 
      print_type_v2 fmt v
  | id, BindType v ->
      fprintf fmt "@[%a:%a@]" Ident.print id print_type_v v; 
  | id, BindSet -> 
      fprintf fmt "%a:Set" Ident.print id
  | id, Untyped -> 
      fprintf fmt "<untyped>"

and print_type_v2 fmt = function
  | Ref v -> 
      fprintf fmt "@[%a@ ref@]" print_type_v v
  | Array v -> 
      fprintf fmt "@[array@ %a@]" print_type_v v
  | PureType pt -> 
      print_pure_type fmt pt
  | Arrow _ as v ->
      fprintf fmt "(%a)" print_type_v v

and print_type_c fmt c =
  let id = c.c_result_name in
  let v = c.c_result_type in
  let p = c.c_pre in
  let q = c.c_post in
  let e = c.c_effect in
  if e = Effect.bottom && p = [] && q = None then
    print_type_v fmt v
  else
    fprintf fmt "@[{%a}@ returns %a: %a@ %a@,{%a}@]" 
      print_pre p
      Ident.print id 
      print_type_v v 
      Effect.print e
      print_post q

let rec print_logic_type fmt lt =
  let print_args = print_list comma print_pure_type in
  match lt with
    | Predicate l -> fprintf fmt "%a -> prop" print_args l
    | Function (l, pt) -> fprintf fmt "%a -> %a" print_args l print_pure_type pt

(*s Pretty-print of typed programs *)

let rec print_prog fmt p = 
  let k = p.info.kappa in
  if k.c_pre = [] && p.info.obligations = [] && k.c_post = None then
    fprintf fmt "@[%s:@,%a@]" p.info.label print_desc p.desc
  else
  fprintf fmt "@[<hv>[%d-%d]%s:@,@[{%a;%a}@]@ @[%a@]@ @[{%a}@]@]" 
    (fst p.info.loc) (snd p.info.loc)
    p.info.label print_pre k.c_pre print_pre p.info.obligations 
    print_desc p.desc print_post k.c_post

and print_desc fmt = function
  | Var id -> 
      Ident.print fmt id
  | Acc id -> 
      fprintf fmt "!%a" Ident.print id
  | Aff (id, p) -> 
      fprintf fmt "@[%a :=@ %a@]" Ident.print id print_prog p
  | TabAcc (_, id, p) -> 
      fprintf fmt "%a[%a]" Ident.print id print_prog p
  | TabAff (_, id, p1, p2) -> 
      fprintf fmt "%a[%a] :=@ %a" Ident.print id print_prog p1 print_prog p2
  | Seq bl -> 
      fprintf fmt "@[begin@\n  @[%a@]@\nend@]" print_block bl
  | While (p, i, var, e) ->
      fprintf fmt 
	"while %a do@\n  { invariant @[%a@] variant _ }@\n  @[%a@]@\ndone" 
	print_prog p (print_option print_assertion) i print_prog e
  | If (p1, p2, p3) ->
      fprintf fmt "@[if %a then@ %a else@ %a@]" 
	print_prog p1 print_prog p2 print_prog p3
  | Lam (bl, p) -> 
      fprintf fmt "@[fun <bl> ->@\n  %a@]" print_prog p
  | App (p, a, k) -> 
      fprintf fmt "(@[%a %a ::@ %a@])" print_prog p print_arg a print_type_c k
  | LetRef (id, p1, p2) ->
      fprintf fmt "@[<hv>@[<hv 2>let %a =@ ref %a@ in@]@ %a@]" 
	Ident.print id print_prog p1 print_prog p2
  | LetIn (id, p1, p2) ->
      fprintf fmt "@[<hv>@[<hv 2>let %a =@ %a in@]@ %a@]" 
	Ident.print id print_prog p1 print_prog p2
  | Rec (id, bl, v, var, p) ->
      fprintf fmt "rec %a : <bl> %a { variant _ } =@\n%a" 
	Ident.print id print_type_v v print_prog p
  | Raise (id, None) ->
      fprintf fmt "raise %a" Ident.print id
  | Raise (id, Some p) ->
      fprintf fmt "raise (%a %a)" Ident.print id print_prog p
  | Try (p, hl) ->
      fprintf fmt "@[<hv>try@ %a@ with %a@ end@]" print_prog p 
	(print_list alt print_handler) hl
  | Expression t -> 
      print_term fmt t
  | Absurd ->
      fprintf fmt "absurd"
  | Any k ->
      fprintf fmt "[%a]" print_type_c k

and print_handler fmt ((id, a), e) = match a with
  | None -> 
      fprintf fmt "%a ->@ %a" Ident.print id print_prog e
  | Some a -> 
      fprintf fmt "%a %a ->@ %a" Ident.print id Ident.print a print_prog e

and print_cast fmt = function
  | None -> ()
  | Some v -> fprintf fmt ": %a" print_type_v v

and print_block fmt = 
  print_list (fun fmt () -> fprintf fmt ";@\n") print_block_st fmt

and print_block_st fmt = function
  | Statement p -> print_prog fmt p
  | Label l -> fprintf fmt "label %s" l
  | Assert a -> fprintf fmt "@[assert@ @[{ %a }@]@]" print_assertion a

and print_arg fmt = function
  | Term p -> print_prog fmt p
  | Refarg id -> Ident.print fmt id
  | Type v -> print_type_v fmt v

(*s Pretty-print of cc-terms (intermediate terms) *)

let print_pred_binders = ref true
let print_var_binders = ref false

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray t -> 
      fprintf fmt "(array %a)" print_cc_type t
  | TTlambda (b, t) ->
      fprintf fmt "[%a]%a" print_binder b print_cc_type t
  | TTarrow (b, t) -> 
      fprintf fmt "(%a)%a" print_binder b print_cc_type t
  | TTtuple (bl, None) -> 
      fprintf fmt "{%a}" print_tuple bl
  | TTtuple (bl, Some q) -> 
      fprintf fmt "{%a | %a}" print_tuple bl print_cc_type q
  | TTpred p ->
      print_predicate fmt p
  | TTapp (tt, l) ->
      fprintf fmt "(%a %a)" print_cc_type tt (print_list space print_cc_type) l
  | TTterm t ->
      print_term fmt t
  | TTSet -> 
      fprintf fmt "Set"

and print_tuple fmt = print_list comma print_binder fmt

and print_binder fmt (id,b) = 
  Ident.print fmt id;
  match b with
    | CC_pred_binder p -> 
	if !print_pred_binders then fprintf fmt ": %a" print_predicate p
    | CC_var_binder t -> 
	if !print_var_binders then fprintf fmt ": %a" print_cc_type t
    | CC_untyped_binder -> 
	()

let rec print_cc_pattern fmt = function
  | PPvariable (id, _) -> 
      Ident.print fmt id
  | PPcons (id, pl) -> 
      fprintf fmt "(%a %a)" 
	Ident.print id (print_list space print_cc_pattern) pl

let print_case_pred fmt (x,_) = Ident.print fmt x

let rec print_cc_term fmt = function
  | CC_var id -> 
      fprintf fmt "%s" (Ident.string id)
  | CC_letin (_,bl,c,c1) ->
      fprintf fmt "@[@[<hov 2>let %a =@ %a in@]@\n%a@]"
      (print_list comma print_binder) bl
      print_cc_term c print_cc_term c1
  | CC_lam (b,c) ->
      fprintf fmt "@[<hov 2>[%a]@,%a@]" print_binder b print_cc_term c
  | CC_app (f,a) ->
      fprintf fmt "@[<hov 2>(%a@ %a)@]" print_cc_term f print_cc_term a
  | CC_tuple (cl,_) ->
      fprintf fmt "@[<hov 2>(%a)@]" (print_list comma print_cc_term) cl
  | CC_if (b,e1,e2) ->
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (print_cc_term fmt) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (print_cc_term fmt) e2;
      fprintf fmt "@]"
  | CC_case (e,pl) ->
      fprintf fmt "@[<v>match %a with@\n  @[%a@]@\nend@]" 
	print_cc_term e (print_list newline print_case) pl
  | CC_term c ->
      fprintf fmt "@["; print_term fmt c; fprintf fmt "@]"
  | CC_hole (_, c) ->
      fprintf fmt "@[(?:@ "; print_predicate fmt c; fprintf fmt ")@]"
  | CC_type t ->
      print_cc_type fmt t
  | CC_any t ->
      fprintf fmt "@[(any(%a))@]" print_cc_type t

and print_binders fmt bl =
  print_list nothing (fun fmt b -> fprintf fmt "[%a]" print_binder b) fmt bl

and print_case fmt (p,e) =
  fprintf fmt "@[<hov 2>| %a =>@ %a@]" print_cc_pattern p print_cc_term e

let print_subst fmt =
  Idmap.iter
    (fun id t -> fprintf fmt "%a -> %a@\n" Ident.print id print_term t)

let print_cc_subst fmt =
  Idmap.iter
    (fun id t -> fprintf fmt "%a -> %a@\n" Ident.print id print_cc_term t)


let print_env fmt e =
  let print_type_info fmt = function
    | Set -> fprintf fmt "Set"
    | TypeV v -> print_type_v fmt v
  in
  fold_all (fun (id, v) () -> fprintf fmt "%a:%a, " Ident.dbprint id 
		print_type_info v) e ()

(*s For debugging purposes *)

open Ptree

let rec print_ptree fmt p = match p.pdesc with
  | Svar x -> Ident.print fmt x
  | Srefget x -> fprintf fmt "!%a" Ident.print x
  | Srefset (x, p) -> fprintf fmt "@[%a := %a@]" Ident.print x print_ptree p
  | Sarrget (_, x, p) -> fprintf fmt "%a[%a]" Ident.print x print_ptree p
  | Sarrset (_, x, p1, p2) ->
      fprintf fmt "@[%a[%a] := %a@]" Ident.print x 
	print_ptree p1 print_ptree p2
  | Sseq bl ->
      fprintf fmt "begin@\n  @[%a@]@\nend" print_block bl
  | Swhile (p1, _, _, p2) ->
      fprintf fmt "while %a do@\n  @[%a@]@\ndone" print_ptree p1 print_ptree p2
  | Sif (p1, p2, p3) ->
      fprintf fmt "@[<hv 2>if %a then@ %a else@ %a@]" 
	print_ptree p1 print_ptree p2 print_ptree p3
  | Slam (bl, p) ->
      fprintf fmt "@[<hov 2>fun <...> ->@ %a@]" print_ptree p
  | Sapp (p, a) ->
      fprintf fmt "(%a %a)" print_ptree p print_arg a
  | Sletref (id, e1, e2) -> 
      fprintf fmt "@[let %a = ref %a in@ %a@]" 
	Ident.print id print_ptree e1 print_ptree e2
  | Sletin (id, e1, e2) ->
      fprintf fmt "@[let %a = %a in@ %a@]"
	Ident.print id print_ptree e1 print_ptree e2
  | Srec _ ->
      fprintf fmt "<Srec>"
  | Sraise (x, None, _) -> 
      fprintf fmt "raise %a" Ident.print x
  | Sraise (x, Some e, _) -> 
      fprintf fmt "raise (%a %a)" Ident.print x print_ptree e
  | Stry (e, hl) ->
      fprintf fmt "@[<v>try %a with@\n  @[%a@]@\nend@]" 
	print_ptree e (print_list newline print_phandler) hl
  | Sconst c -> print_term fmt (Tconst c)
  | Sabsurd _ -> fprintf fmt "<Sabsurd>"
  | Sany _ -> fprintf fmt "<Sany>"

and print_phandler fmt = function
  | (x, None), e -> 
      fprintf fmt "| %a => %a" Ident.print x print_ptree e
  | (x, Some y), e -> 
      fprintf fmt "| %a %a => %a" Ident.print x Ident.print y print_ptree e

and print_arg fmt = function
  | Sterm p -> print_ptree fmt p
  | Stype _ -> fprintf fmt "<Stype>"

and print_block_st fmt = function
  | Slabel l -> fprintf fmt "%s:" l
  | Sassert _ -> fprintf fmt "<Sassert>"
  | Sstatement p -> print_ptree fmt p

and print_block fmt =
  print_list (fun fmt () -> fprintf fmt ";@\n") print_block_st fmt

let print_external fmt b = if b then fprintf fmt "external "

let print_decl fmt = function
  | Program (id, p) -> fprintf fmt "let %a = %a" Ident.print id print_ptree p
  | Parameter (_, e, ids, v) -> 
      fprintf fmt "%aparameter <...>" print_external e
  | Exception (_, id, pto) -> fprintf fmt "exception %a <...>" Ident.print id
  | Logic (_, e, ids, lt) -> 
      fprintf fmt "%alogic %a : <...>" print_external e 
	(print_list comma Ident.print) ids
  | Axiom (_, id, p) ->
      fprintf fmt "axiom %a : <...>" Ident.print id
  | Predicate_def (_, id, _, _) ->
      fprintf fmt "predicate %a <...>" Ident.print id

let print_pfile = print_list newline print_decl
