(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: util.ml,v 1.7 2002-02-07 15:11:51 filliatr Exp $ i*)

open Logic
open Ident
open Misc
open Types
open Ast
open Env
open Rename

(* Some generic functions on programs *)

let is_mutable_in_env env id =
  (is_in_env env id) && (is_mutable (type_in_env env id))

let predicate_now_vars env c =
  Idset.filter (is_mutable_in_env env) (predicate_vars c)

let term_now_vars env c =
  Idset.filter (is_mutable_in_env env) (term_vars c)

let gen_change_label f c =
  let ids = Idset.elements (predicate_vars c) in
  let al = 
    map_succeed
      (function id -> 
	 if is_at id then (id, f (un_at id)) else failwith "caught")
      ids
  in
  subst_in_predicate al c

let make_before_after c =
  gen_change_label 
    (function (uid,"") -> uid | _ -> failwith "caught") c

let erase_label l c =
  gen_change_label 
    (function (uid,l') when l = l' -> uid | _ -> failwith "caught") c

let change_label l1 l2 c =
  gen_change_label 
    (function (uid,l) when l = l1 -> at_id uid l2 | _ -> failwith "caught") c

let make_after_before_al env ids =
  Idset.fold 
    (fun id al -> 
       if is_mutable_in_env env id then (id, at_id id "") :: al else al)
    ids []

let make_after_before env p = 
  subst_in_predicate (make_after_before_al env (predicate_vars p)) p

let make_after_before_term env t =
  subst_in_term (make_after_before_al env (term_vars t)) t


(* [apply_pre] and [apply_post] instantiate pre- and post- conditions
 * according to a given renaming of variables (and a date that means
 * `before' in the case of the post-condition).
 *)

let make_assoc_list ren env on_prime ids =
  Idset.fold
    (fun id al ->
       if is_mutable_in_env env id then
	 (id,current_var ren id) :: al
       else if is_at id then
	 let uid,d = un_at id in
	   if is_mutable_in_env env uid then
	     (match d with
		| "" -> (id,on_prime ren uid)
		| _  -> (id,var_at_date ren d uid)) :: al
	   else
	     al
       else
	 al) 
    ids []

let apply_term ren env t =
  let ids = term_vars t in
  let al = make_assoc_list ren env current_var ids in
  subst_in_term al t

let apply_pre ren env c =
  let ids = predicate_vars c.p_value in
  let al = make_assoc_list ren env current_var ids in
  { p_assert = c.p_assert; p_name = c.p_name; 
    p_value = subst_in_predicate al c.p_value }

let apply_assert ren env c =
  let ids = predicate_vars c.a_value in
  let al = make_assoc_list ren env current_var ids in
  { a_name = c.a_name; a_value = subst_in_predicate al c.a_value }
 
let apply_post ren env before c =
  let ids = predicate_vars c.a_value in
  let al = 
    make_assoc_list ren env (fun r uid -> var_at_date r before uid) ids in
  { a_name = c.a_name; a_value = subst_in_predicate al c.a_value }

(* [traverse_binder ren env bl] updates renaming [ren] and environment [env]
 * as we cross the binders [bl]
 *)

let rec traverse_binders env = function
  | [] -> env
  | (id,BindType v)::rem ->
      traverse_binders (add (id,v) env) rem
  | (id,BindSet)::rem ->
      traverse_binders (add_set id env) rem
  | (_,Untyped)::_ ->
      invalid_arg "traverse_binders"
	  
let initial_renaming env =
  let ids = Env.fold_all (fun (id,_) l -> id::l) env [] in
  update empty_ren "0" ids


(* Substitutions *)

let rec type_c_subst s c =
  let {c_result_name=id; c_result_type=t; c_effect=e; c_pre=p; c_post=q} = c in
  let s' = s @ List.map (fun (x,x') -> (at_id x "", at_id x' "")) s in
  { c_result_name = id;
    c_result_type = type_v_subst s t;
    c_effect = Effect.subst s e;
    c_pre = List.map (pre_app (subst_in_predicate s)) p;
    c_post = option_app (post_app (subst_in_predicate s')) q }

and type_v_subst s = function
  | Ref v -> Ref (type_v_subst s v)
  | Array (n,v) -> Array (n,type_v_subst s v)
  | Arrow (bl,c) -> Arrow (List.map (binder_subst s) bl, type_c_subst s c)
  | (PureType _) as v -> v

and binder_subst s = function
  | (n, BindType v) -> (n, BindType (type_v_subst s v))
  | b -> b

(* substitution of term for variables *)

let rec type_c_rsubst s c =
  { c_result_name = c.c_result_name;
    c_result_type = type_v_rsubst s c.c_result_type;
    c_effect = c.c_effect;
    c_pre = List.map (pre_app (tsubst_in_predicate s)) c.c_pre;
    c_post = option_app (post_app (tsubst_in_predicate s)) c.c_post }

and type_v_rsubst s = function
  | Ref v -> Ref (type_v_rsubst s v)
  | Array (n,v) -> Array (tsubst_in_term s n, type_v_rsubst s v)
  | Arrow (bl,c) -> Arrow(List.map (binder_rsubst s) bl, type_c_rsubst s c)
  | PureType _ as v -> v

and binder_rsubst s = function
  | (n, BindType v) -> (n, BindType (type_v_rsubst s v))
  | b -> b

(* make_arrow bl c = (x1:V1)...(xn:Vn)c *)

let make_arrow bl c = match bl with
  | [] -> invalid_arg "make_arrow: no binder"
  | _ -> Arrow (bl,c)

(* misc. functions *)

let deref_type = function
  | Ref v -> v
  | _ -> invalid_arg "deref_type"

let dearray_type = function
  | Array (size,v) -> size,v
  | _ -> invalid_arg "dearray_type"

let decomp_kappa c = 
  ((c.c_result_name, c.c_result_type), c.c_effect, c.c_pre, c.c_post)

let id_from_name = function Name id -> id | Anonymous -> (Ident.create "X")

(* [decomp_boolean c] returns the specs R and S of a boolean expression *)

let decomp_boolean = function
  | Some { a_value = c } -> 
      (* q -> if result then q(true) else q(false) *)
      let ctrue = tsubst_in_predicate [Ident.result,ttrue] c in
      let cfalse = tsubst_in_predicate [Ident.result,tfalse] c in
      ctrue, cfalse
  | _ -> 
      assert false

(* [make_access env id c] Access in array id.
 *
 * Constructs [t:(array s T)](access_g s T t c ?::(lt c s)).
 *)

let array_info env id =
  let ty = type_in_env env id in
  let size,v = dearray_type ty in
  (*i let ty_elem = trad_ml_type_v ren env v in
  let ty_array = trad_imp_type ren env ty in i*)
  size,v

let make_raw_access env (id,id') c =
  let size,_ = array_info env id in
  Tapp (Ident.access, [Tvar id'; c])

let make_pre_access env id c =
  let size,_ = array_info env id in
  Pand (le (Tconst (ConstInt 0)) c, lt c size)
      
let make_raw_store env (id,id') c1 c2 =
  let size,_ = array_info env id in
  Tapp (Ident.store, [Tvar id'; c1; c2])

(*s Pretty printers (for debugging purposes) *)

open Format

let print_pre fmt l = 
  if l <> [] then begin
    fprintf fmt "@[pre@ ";
    print_list 
      fmt pp_print_space (fun fmt p -> print_predicate fmt p.p_value) l;
    fprintf fmt "@]"
  end

let print_post fmt = function
  | None -> 
      ()
  | Some c -> 
      fprintf fmt "@[post@ "; print_predicate fmt c.a_value; fprintf fmt "@]"

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTfloat -> fprintf fmt "float"
  | PTarray (s,t) -> 
      fprintf fmt "array("; print_term fmt s; fprintf fmt ","; 
      print_pure_type fmt t; fprintf fmt ")"
  | PTexternal id -> fprintf fmt "%s" (Ident.string id)

and print_type_v fmt = function
  | Ref v -> 
      fprintf fmt "@["; print_type_v fmt v; fprintf fmt "@ ref@]"
  | Array (cc,v) -> 
      fprintf fmt "@[array"; print_term fmt cc; fprintf fmt "@ of ";
      print_type_v fmt v; fprintf fmt "@]"
  | Arrow (b,c) ->
      fprintf fmt "@["; print_list fmt (fun _ _ -> ()) pp_binder b;
      fprintf fmt "@,"; print_type_c fmt c; fprintf fmt "@]"
  | PureType pt -> 
      print_pure_type fmt pt

and print_type_c fmt c =
  let id = c.c_result_name in
  let v = c.c_result_type in
  fprintf fmt "@[returns %s: " (Ident.string id);
  print_type_v fmt v; fprintf fmt "@ ";
  Effect.print fmt c.c_effect; fprintf fmt "@ ";
  print_pre fmt c.c_pre; fprintf fmt "@ ";
  print_post fmt c.c_post; fprintf fmt " end@]"

and pp_binder fmt = function
  | id,BindType v -> 
      fprintf fmt "(@[%s:@ " (Ident.string id); 
      print_type_v fmt v; fprintf fmt "@])"
  | id,BindSet -> 
      fprintf fmt "(%s: Set)" (Ident.string id)
  | id,Untyped -> 
      fprintf fmt "(%s)" (Ident.string id)

(*s Pretty-print of cc-terms (intermediate terms) *)

let print_pred_binders = ref true

let print_binder fmt = function
  | CC_pred_binder p -> 
      if !print_pred_binders then begin
	fprintf fmt ": "; print_predicate fmt p
      end
  | _ -> 
      ()

let rec print_cc_term fmt = function
  | CC_var id -> 
      fprintf fmt "%s" (Ident.string id)
  | CC_letin (_,bl,c,c1) ->
      fprintf fmt "@[@[<hov 2>let ";
      print_list fmt comma 
	(fun fmt (id,b) -> Ident.print fmt id; print_binder fmt b) bl;
      fprintf fmt " =@ "; print_cc_term fmt c;
      fprintf fmt " in@]@\n"; print_cc_term fmt c1; fprintf fmt "@]"
  | CC_lam (bl,c) ->
      fprintf fmt "@[<hov 2>";
      print_binders fmt bl;
      fprintf fmt "@,"; print_cc_term fmt c; fprintf fmt "@]"
  | CC_app (f,args) ->
      fprintf fmt "@[<hov 2>("; 
      print_cc_term fmt f; fprintf fmt "@ ";
      print_list fmt pp_print_space print_cc_term args;
      fprintf fmt ")@]"
  | CC_tuple cl ->
      fprintf fmt "@[<hov 2>(";
      print_list fmt comma print_cc_term cl;
      fprintf fmt ")@]"
  | CC_case (b,[bl1,e1; bl2,e2]) ->
      let branch bl e =
	print_binders fmt bl; fprintf fmt "@,"; print_cc_term fmt e in
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (branch bl1) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (branch bl2) e2;
      fprintf fmt "@]"
  | CC_case _ ->
      fprintf fmt "<Case...>"
  | CC_if (b,e1,e2) ->
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (print_cc_term fmt) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (print_cc_term fmt) e2;
      fprintf fmt "@]"
  | CC_expr c ->
      fprintf fmt "@["; print_term fmt c; fprintf fmt "@]"
  | CC_hole c ->
      fprintf fmt "@[(?:@ "; print_predicate fmt c; fprintf fmt ")@]"

and print_binders fmt bl =
  print_list fmt nothing 
    (fun fmt (id,b) -> 
       fprintf fmt "[%s" (Ident.string id);
       print_binder fmt b; fprintf fmt "]") 
    bl
