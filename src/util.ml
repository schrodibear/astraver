
(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id: util.ml,v 1.2 2001-08-17 00:52:40 filliatr Exp $ *)

open Logic
open Ident
open Misc
open Types
open Ast
open Env
open Rename

(*s Various utility functions. *)
let map_succeed f = 
  let rec map_f = function 
    | [] -> []
    |  h::t -> try (let x = f h in x :: map_f t) with Failure _ -> map_f t
  in 
  map_f 

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function PureType _ -> true | _ -> false

let named_app f x = { a_name = x.a_name; a_value = (f x.a_value) }

let pre_app f x = 
  { p_assert = x.p_assert; p_name = x.p_name; p_value = f x.p_value }

let post_app = named_app

let anonymous x = { a_name = Anonymous; a_value = x }

let anonymous_pre b x = { p_assert = b; p_name = Anonymous; p_value = x }

let force_name f x =
  option_app (fun q -> { a_name = Name (f q.a_name); a_value = q.a_value }) x

let force_post_name x = force_name post_name x

let force_bool_name x = 
  force_name (function Name id -> id | Anonymous -> bool_name()) x

let out_post = function
    Some { a_value = x } -> x
  | None -> invalid_arg "out_post"

let pre_of_assert b x =
  { p_assert = b; p_name = x.a_name; p_value = x.a_value }

let assert_of_pre x =
  { a_name = x.p_name; a_value = x.p_value }

(* Some generic functions on programs *)

let is_mutable_in_env env id =
  (is_in_env env id) && (is_mutable (type_in_env env id))

let predicate_now_vars env c =
  Idset.filter (is_mutable_in_env env) (predicate_vars c)

let term_now_vars env c =
  Idset.filter (is_mutable_in_env env) (term_vars c)

let make_before_after c =
  let ids = Idset.elements (predicate_vars c) in
  let al = 
    map_succeed
      (function id -> 
	 if is_at id then 
	   match un_at id with (uid,"") -> (id,uid) | _ -> failwith "caught"
	 else failwith "caught")
      ids
  in
  subst_in_predicate al c

(* [apply_pre] and [apply_post] instantiate pre- and post- conditions
 * according to a given renaming of variables (and a date that means
 * `before' in the case of the post-condition).
 *)

let make_assoc_list ren env on_prime ids =
  Idset.fold
    (fun id al ->
       if is_mutable_in_env env id then
	 (id,current_var ren id)::al
       else if is_at id then
	 let uid,d = un_at id in
	   if is_mutable_in_env env uid then
	     (match d with
		  "" -> (id,on_prime ren uid)
		| _  -> (id,var_at_date ren d uid))::al
	   else
	     al
       else
	 al) 
    ids []

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

let id_from_name = function Name id -> id | Anonymous -> (Ident.create "X")

(* v_of_constr : traduit un type CCI en un type ML *)
(*i
let dest_sig c = match matches (Coqlib.build_coq_sig_pattern ()) c with
  | [_,a; _,p] -> (a,p)
  | _     -> assert false

(* TODO: faire un test plus serieux sur le type des objets Coq *)
let rec is_pure_cci c = match kind_of_term c with
  | IsCast (c,_) -> is_pure_cci c
  | IsProd(_,_,c') -> is_pure_cci c'
  | IsRel _ | IsMutInd _ | IsConst _ -> true (* heu... *)
  | IsApp _ -> not (is_matching (Coqlib.build_coq_sig_pattern ()) c)
  | _ -> Util.error "CCI term not acceptable in programs"

let rec v_of_constr c = match kind_of_term c with
  | IsCast (c,_) -> v_of_constr c
  | IsProd _ ->
      let revbl,t2 = Term.decompose_prod c in
      let bl =
	List.map
	  (fun (name,t1) -> (id_from_name name, BindType (v_of_constr t1)))
	  (List.rev revbl)
      in
      let vars = List.rev (List.map (fun (id,_) -> mkVar id) bl) in
      Arrow (bl, c_of_constr (substl vars t2))
  | IsMutInd _ | IsConst _ | IsApp _ ->
      PureType c
  | _ -> 
      failwith "v_of_constr: TODO"

and c_of_constr c =
  if is_matching (Coqlib.build_coq_sig_pattern ()) c then
    let (a,q) = dest_sig c in
    (result_id, v_of_constr a), Effect.bottom, [], Some (anonymous q)
  else
    (result_id, v_of_constr c), Effect.bottom, [], None
i*)

(* [make_access env id c] Access in array id.
 *
 * Constructs [t:(array s T)](access_g s T t c ?::(lt c s)).
 *)

let array_info ren env id =
  let ty = type_in_env env id in
  let size,v = dearray_type ty in
  (*i let ty_elem = trad_ml_type_v ren env v in
  let ty_array = trad_imp_type ren env ty in i*)
  size,v

let make_raw_access ren env (id,id') c =
  let size,_ = array_info ren env id in
  Tapp (Ident.access, [Tvar id'; c])

let make_pre_access ren env id c =
  let size,_ = array_info ren env id in
  Pand (Pterm (Tapp (Ident.t_le, [Tconst (ConstInt 0); c])),
	Pterm (Tapp (Ident.t_lt, [c; size])))
      
let make_raw_store ren env (id,id') c1 c2 =
  let size,_ = array_info ren env id in
  Tapp (Ident.store, [Tvar id'; c1; c2])

(* pretty printers (for debugging purposes) *)

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
  | PTexternal id -> fprintf fmt "%s" (Ident.string id)

and print_type_v fmt = function
  | Ref v -> 
      fprintf fmt "@["; print_type_v fmt v; fprintf fmt "@ ref@]"
  | Array (cc,v) -> 
      fprintf fmt "@[array"; print_term fmt cc; fprintf fmt "@ of ";
      print_type_v fmt v; fprintf fmt "@]"
  | Arrow (b,c) ->
      fprintf fmt "@["; print_list fmt (fun _ _ -> ()) pp_binder b;
      print_type_c fmt c; fprintf fmt "@]"
  | PureType pt -> 
      print_pure_type fmt pt

and print_type_c fmt c =
  let id = c.c_result_name in
  let v = c.c_result_type in
  fprintf fmt "@[returns %s: " (Ident.string id);
  print_type_v fmt v; fprintf fmt "@ ";
  Effect.print fmt c.c_effect; fprintf fmt "@ ";
  print_pre fmt c.c_pre; fprintf fmt "@ ";
  print_post fmt c.c_post; fprintf fmt "end@]"

and pp_binder fmt = function
  | id,BindType v -> 
      fprintf fmt "(@[%s:@ " (Ident.string id); 
      print_type_v fmt v; fprintf fmt "@])"
  | id,BindSet -> 
      fprintf fmt "(%s: Set)" (Ident.string id)
  | id,Untyped -> 
      fprintf fmt "(%s)" (Ident.string id)

(* pretty-print of cc-terms (intermediate terms) *)

let print_cc_term fmt c = fprintf fmt "<cc_term>"

(*i
let rec pp_cc_term = function
  | CC_var id -> pr_id id
  | CC_letin (_,_,bl,c,c1) ->
      hOV 0 [< hOV 2 [< 'sTR"let ";
		  	prlist_with_sep (fun () -> [< 'sTR"," >])
			  (fun (id,_) -> pr_id id) bl;
		  	'sTR" ="; 'sPC;
		  	pp_cc_term c;
		  	'sTR " in">];
	       'fNL;
	       pp_cc_term c1 >]
  | CC_lam (bl,c) ->
      hOV 2 [< prlist (fun (id,_) -> [< 'sTR"["; pr_id id; 'sTR"]" >]) bl;
	       'cUT;
	       pp_cc_term c >]
  | CC_app (f,args) ->
      hOV 2 [< 'sTR"("; 
	       pp_cc_term f; 'sPC;
	       prlist_with_sep (fun () -> [< 'sPC >]) pp_cc_term args;
	       'sTR")" >]
  | CC_tuple (_,_,cl) ->
      hOV 2 [< 'sTR"(";
	       prlist_with_sep (fun () -> [< 'sTR","; 'cUT >])
		 pp_cc_term cl;
	       'sTR")" >]
  | CC_case (_,b,[e1;e2]) ->
      hOV 0 [< 'sTR"if "; pp_cc_term b; 'sTR" then"; 'fNL;
	       'sTR"  "; hOV 0 (pp_cc_term e1); 'fNL;
	       'sTR"else"; 'fNL;
	       'sTR"  "; hOV 0 (pp_cc_term e2) >]
  | CC_case _ ->
      hOV 0 [< 'sTR"<Case: not yet implemented>" >]
  | CC_expr c ->
      hOV 0 (prterm c)
  | CC_hole c ->
      [< 'sTR"(?::"; prterm c; 'sTR")" >]
i*)

