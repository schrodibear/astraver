(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: typing.ml,v 1.34 2002-03-18 16:20:29 filliatr Exp $ i*)

(*s Typing. *)

open Format
open Options
open Ident
open Misc
open Util
open Logic
open Rename
open Types
open Ast
open Env 
open Effect

module LabelSet = Set.Make(struct type t = string let compare = compare end)

let initial_labels = LabelSet.singleton "0"

(*s Typing of terms (used to type pure expressions). *)

let type_v_int = PureType PTint
let type_v_bool = PureType PTbool
let type_v_unit = PureType PTunit
let type_v_float = PureType PTfloat

let rec typing_term loc env = function
  | Tvar id -> 
      (try 
	 (match type_in_env env id with Ref v -> v | v -> v)
       with Not_found ->
	 Error.unbound_variable id (Some loc))
  | Tconst (ConstInt _) -> type_v_int
  | Tconst (ConstBool _) -> type_v_bool
  | Tconst ConstUnit -> type_v_unit
  | Tconst (ConstFloat _) -> type_v_float
  | Tapp (id, [a;b]) when id == t_eq || id == t_neq ->
      check_same_type loc env a b; type_v_bool
  | Tapp (id, tl) as t ->
      if not (is_in_env env id) then Error.app_of_non_function loc;
      (match type_in_env env id with
	 | Arrow (bl, c) ->
	     let ttl = List.map (fun t -> (t, typing_term loc env t)) tl in
	     check_app loc bl c ttl
	 | _ -> 
	     Error.app_of_non_function loc)
  | Tbound _ ->
      assert false

and check_same_type loc env a b =
  let ta = typing_term loc env a in
  let tb = typing_term loc env b in
  if ta <> tb then 
    Error.term_expected_type loc 
      (fun fmt -> print_term fmt b) (fun fmt -> print_type_v fmt ta)

and check_app loc bl c tl = match bl, tl with
  | [], [] ->
      c.c_result_type
  | _, [] ->
      Arrow (bl, c)
  | [], _ ->
      Error.too_many_arguments loc
  | (_,BindType et) :: bl , (a,at) :: tl ->
      if et <> at then 
	Error.term_expected_type loc 
	  (fun fmt -> print_term fmt a) (fun fmt -> print_type_v fmt et);
      check_app loc bl c tl
  | _ ->
      assert false

(*s Checking types *)

let check_predicate loc lab env p =
  let vars = predicate_vars p in
  Idset.iter
    (if_labelled 
       (fun (_,l) -> 
	  if not (LabelSet.mem l lab) then Error.unbound_label l loc))
    vars

let check_pre loc lab env p = check_predicate loc lab env p.p_value

let check_post loc lab env a = 
  let lab' = LabelSet.add "" lab in check_predicate loc lab' env a.a_value

let check_effect loc env e =
  let check_ref id =
    if not (Env.is_ref env id) then Error.unbound_reference id loc
  in
  let r,w = Effect.get_repr e in
  List.iter check_ref r;
  List.iter check_ref w

let rec check_type_v loc lab env = function
  | Ref v -> 
      check_type_v loc lab env v
  | Array (t, v) -> 
      check_type_v loc lab env v
  | Arrow (bl, c) -> 
      let env' = check_binders loc lab env bl in check_type_c loc lab env' c
  | PureType _ -> 
      ()

and check_type_c loc lab env c =
  check_effect loc env c.c_effect;
  check_type_v loc lab env c.c_result_type;
  List.iter (check_pre loc lab env) c.c_pre;
  option_iter (check_post loc lab env) c.c_post

and check_binders loc lab env = function
  | [] ->
      env
  | (id, BindType v) :: bl ->
      check_type_v loc lab env v;
      check_binders loc lab (Env.add id v env) bl
  | (id, BindSet) :: bl ->
      check_binders loc lab (Env.add_set id env) bl
  | (id, Untyped) :: bl ->
      check_binders loc lab env bl

(*s Utility functions for typing *)

let just_reads e = difference (get_reads e) (get_writes e)

let type_v_sup loc t1 t2 =
  if t1 <> t2 then Error.if_branches loc;
  t1

let typed_var loc env var = var
(*i todo: type variants
let typed_var loc env (phi,r) = 
  match typing_term loc env phi with
    | PureType t -> (phi, r, t)
    | _ -> Error.raise_with_loc (Some loc) 
   	     (Error.AnyMessage "A variant must have a pure type")
***i*)

(* TODO: subtype is currently structural equality *)
let rec subtype = function
  | (PureType c1, PureType c2) -> 
      c1 = c2
  | (Ref v1, Ref v2) -> 
      subtype (v1,v2)
  | (Array (s1,v1), Array (s2,v2)) -> 
      s1 = s2 && subtype (v1,v2)
  | (v1,v2) -> 
      v1 = v2

let union3effects x y z = Effect.union x (Effect.union y z)

let decomp_fun_type f tf = match tf.info.kappa.c_result_type with
  | Arrow ([x,BindType v], k) ->
      x, v, k
  | Arrow ((x,BindType v) :: bl, k) ->
      x, v, type_c_of_v (Arrow (bl, k))
  | Arrow ((x,_) :: _, _) ->
      Error.expects_a_term x f.info.loc
  | Arrow ([], _) ->
      assert false
  | _ -> 
      Error.app_of_non_function f.info.loc

let expected_type loc t et =
  if t <> et then Error.expected_type loc (fun fmt -> print_type_v fmt et)

let check_for_alias loc id v = 
  if occur_type_v id v then Error.raise_with_loc (Some loc) (Error.Alias id)

let type_eq loc = function
  | PureType PTint -> Ident.t_eq_int
  | PureType PTbool -> Ident.t_eq_bool
  | PureType PTfloat -> Ident.t_eq_float
  | PureType PTunit -> Ident.t_eq_unit
  | _ -> Error.expected_type loc 
	 (fun fmt -> fprintf fmt "unit, bool, int or float")

let type_neq loc = function
  | PureType PTint -> Ident.t_neq_int
  | PureType PTbool -> Ident.t_neq_bool
  | PureType PTfloat -> Ident.t_neq_float
  | PureType PTunit -> Ident.t_neq_unit
  | _ -> Error.expected_type loc 
	 (fun fmt -> fprintf fmt "unit, bool, int or float")

let type_eq_neq id =
  assert (is_eq_neq id);
  if id == t_eq then type_eq else type_neq

let make_node p env l k = 
  { desc = p; info = { env = env; label = l; kappa = k } }

let coerce p env k = 
  let l = label_name () in Coerce (make_node p env l k)

let make_arrow_type lab bl k =
  let k = 
    let q = optpost_app (change_label lab "") k.c_post in
    { k with c_post = q }
  in
  make_arrow bl k

(*s Typing variants. 
    Return the effect i.e. variables appearing in the variant. *)

let state_var lab env (phi,r) = 
  let ids = term_refs env phi in
  Effect.add_reads ids Effect.bottom
	
(*s Typing preconditions.
    Return the effect i.e. variables appearing in the precondition. 
    Check existence of labels. *)

let state_pre lab env loc pl =
  let state e p =
    let ids = predicate_vars p.p_value in
    Idset.fold
      (fun id e ->
	 if is_reference env id then
	   Effect.add_read id e
	 else if is_at id then begin
	   let uid,l = un_at id in
	   if not (LabelSet.mem l lab) then Error.unbound_label l loc;
	   if is_reference env uid then
	     Effect.add_read uid e
	   else
	     e
	 end else
	   e)
      ids e 
  in
  List.fold_left state Effect.bottom pl 

let state_assert lab env loc a =
  let p = pre_of_assert true a in
  state_pre lab env loc [p]

let state_inv lab env loc = function
  | None -> Effect.bottom
  | Some i -> state_assert lab env loc i
	  

(*s Typing postconditions.
    Return the effect i.e. variables appearing in the postcondition,
    together with the normalized postcondition (i.e. [x] replaced by [x@]
    whenever [x] is not modified by the program).
    Check existence of labels. *)

let state_post lab env (id,v,ef) loc = function
  | None -> 
      Effect.bottom, None
  | Some q ->
      let ids = predicate_vars q.a_value in
      let ef,c = 
	Idset.fold
	  (fun id (e,c) ->
	     if is_reference env id then
	       if is_write ef id then
		 Effect.add_write id e, c
	       else
		 Effect.add_read id e,
		 subst_in_predicate [id, at_id id ""] c
	     else if is_at id then begin
	       let uid,l = un_at id in
	       if l <> "" && not (LabelSet.mem l lab) then 
		 Error.unbound_label l loc;
	       if is_reference env uid then
		 Effect.add_read uid e, c
	       else
		 Error.unbound_reference uid loc
	     end else
	       e,c)
	  ids (Effect.bottom, q.a_value)
      in
      ef, Some { a_name = q.a_name; a_value = c }


(*s Detection of pure functions. *)

let rec is_pure_type_v = function
  | PureType _ -> true
  | Arrow (bl,c) -> List.for_all is_pure_arg bl && is_pure_type_c c
  | Ref _ | Array _ -> false
and is_pure_arg = function
  | (_,BindType v) -> is_pure_type_v v
  | (_,BindSet) -> true
  | (_,Untyped) -> false
and is_pure_type_c c =
  is_pure_type_v c.c_result_type && c.c_effect = Effect.bottom &&
  c.c_pre = [] && c.c_post = None

(*s Preconditions for partial functions. *)

let partial_pre = function
  | Tapp (id, [a;b]) when id == t_div ->
      let p = neq b (Tconst (ConstInt 0)) in
      [anonymous_pre true p]
  | Tapp (id, [a]) when id == t_sqrt ->
      let p = ge a (Tconst (ConstInt 0)) in
      [anonymous_pre true p]
  | _ ->
      []

let assert_pre p = { p with p_assert = true }

(*s Typing programs. We infer here the type with effects. 
    [lab] is the set of labels, [env] the environment 
    and [expr] the program. *)

let rec typef lab env expr =
  let (d,(v,e),p1) = typef_desc lab env expr.info.loc expr.desc in
  let loc = Some expr.info.loc in
  let ep = state_pre lab env loc expr.info.pre in
  let (eq,q) = state_post lab env (result,v,e) loc expr.info.post in
  let toplabel = label_name () in
  let e' = Effect.union e (Effect.union ep eq) in
  let p' = List.map assert_pre p1 @ expr.info.pre in
  match q, d with
    | None, Coerce expr' ->
	let c = { c_result_name = result; c_result_type = v;
		  c_effect = Effect.union e' (effect expr');
		  c_pre = p' @ (pre expr'); c_post = post expr' } in
	make_node expr'.desc env toplabel c
    | None, App (_,_,Some k') ->
	let c = { c_result_name = result; c_result_type = v; c_effect = e'; 
		  c_pre = p'; c_post = k'.c_post } in
	make_node d env toplabel c
    | _ ->
	let c = { c_result_name = result; c_result_type = v;
		  c_effect = e'; c_pre = p'; c_post = q } in
	make_node d env toplabel c

and typef_desc lab env loc = function
  | Expression c ->
      let v = typing_term loc env c in
      Expression c, (v,Effect.bottom), []

  | Var id as s ->
      let v = type_in_env env id in
      let ef = Effect.bottom in
      let s = if is_pure_type_v v then Expression (Tvar id) else s in
      s, (v,ef), []

  | Acc id ->
      let v = deref_type (type_in_env env id) in
      let ef = Effect.add_read id Effect.bottom in
      Expression (Tvar id), (v,ef), []

  | Aff (x, e1) ->
      let et = type_in_env env x in
      Error.check_for_reference loc x et;
      let t_e1 = typef lab env e1 in
      expected_type e1.info.loc (result_type t_e1) (deref_type et);
      let e = t_e1.info.kappa.c_effect in
      let ef = add_write x e in
      let v = type_v_unit in
      Aff (x, t_e1), (v,ef), []

  | TabAcc (check, x, e) ->
      let t_e = typef lab env e in
      let efe = t_e.info.kappa.c_effect in
      let ef = Effect.add_read x efe in
      let _,ty = dearray_type (type_in_env env x) in
      let s,p = match t_e.desc with
	| Expression c when t_e.info.kappa.c_post = None ->
	    let t = make_raw_access env (x,x) c in
	    let pre = anonymous_pre true (make_pre_access env x c) in
	    Expression t, pre :: t_e.info.kappa.c_pre
	| _ ->
	    TabAcc (check, x, t_e), []
      in
      s, (ty, ef), p

  | TabAff (check, x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      let t_e2 = typef lab env e2 in 
      let ef1 = t_e1.info.kappa.c_effect in
      let ef2 = t_e2.info.kappa.c_effect in
      let ef = Effect.add_write x (Effect.union ef1 ef2) in
      let v = type_v_unit in
      TabAff (check, x, t_e1, t_e2), (v,ef), []

  | Seq bl ->
      let bl,v,ef = typef_block lab env bl in
      Seq bl, (v,ef), []
	      
  | While (b, invopt, var, e) ->
      let efphi = state_var lab env var in
      let t_b = typef lab env b in
      let efb = t_b.info.kappa.c_effect in
      Error.check_no_effect b.info.loc t_b.info.kappa.c_effect;
      let t_e = typef lab env e in
      let efe = t_e.info.kappa.c_effect in
      let efinv = state_inv lab env (Some loc) invopt in
      let ef = 
	Effect.union (Effect.union efe efb) (Effect.union efinv efphi)
      in
      let v = type_v_unit in
      While (t_b,invopt,var,t_e), (v,ef), []
      
  | Lam ([],_) ->
      assert false

  | Lam (bl, e) ->
      let env' = check_binders (Some loc) lab env bl in
      let t_e = typef initial_labels env' e in
      let v = make_arrow_type t_e.info.label bl t_e.info.kappa in
      let ef = Effect.bottom in
      Lam (bl,t_e), (v,ef), []

  | App (_, _, Some _) ->
      assert false

  | App ({desc=Var id} as e, Term a, None) when is_eq_neq id ->
      let t_a = typef lab env a in
      let eq = type_eq_neq id a.info.loc (result_type t_a) in
      typef_desc lab env loc (App ({e with desc = Var eq}, Term a, None))
      (* TODO: avoid recursive call *)
	 
  | App (f, Term a, None) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let t_a = typef lab env a in
      expected_type a.info.loc (result_type t_a) tx;
      let _,eapp,_,_ = decomp_kappa kapp in
      let ef = union3effects (effect t_a) (effect t_f) eapp in
      (match t_a.desc with
	 | Expression ca when post t_a = None && pre t_a = [] ->
	     let kapp = type_c_rsubst [x,ca] kapp in
	     let (_,tapp),_,_,_ = decomp_kappa kapp in
	     (match t_f.desc with
		| Expression cf when t_f.info.kappa.c_post = None ->
		    let pl = (pre t_a) @ (pre t_f) in
		    let e = Expression (applist cf [ca]) in
		    coerce e env kapp, (tapp, ef), pl
		| _ ->	   
		    App (t_f, Term t_a, Some kapp), (tapp, ef), [])
	 | _ ->
	     let (_,tapp),_,_,_ = decomp_kappa kapp in
	     if occur_type_v x tapp then Error.too_complex_argument a.info.loc;
	     (* TODO: rename [x] to avoid capture *)
	     let info = { loc = loc; pre = []; post = None } in
	     let var_x = { desc = Var x; info = info } in
	     let app_f_x = 
	       { desc = App (f, Term var_x, Some kapp); info = info } 
	     in
	     typef_desc lab env loc (LetIn (x, a, app_f_x)))

  | App (f, (Refarg (locr,r) as a), None) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let tr = type_in_env env r in
      expected_type locr tr tx;
      check_for_alias locr r (result_type t_f);
      let kapp = type_c_subst [x,r] kapp in
      let (_,tapp),eapp,_,_ = decomp_kappa kapp in
      let ef = Effect.union (effect t_f) eapp in
      App (t_f, a, Some kapp), (tapp, ef), []

  | App (f, Type _, None) ->
      failwith "todo: typing: application to a type"
      
  | LetRef (x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      let ef1 = t_e1.info.kappa.c_effect in
      let v1 = t_e1.info.kappa.c_result_type in
      let env' = add x (Ref v1) env in
      let t_e2 = typef lab env' e2 in
      let ef2 = t_e2.info.kappa.c_effect in
      let v2 = t_e2.info.kappa.c_result_type in
      Error.check_for_let_ref loc v2;
      let ef = Effect.union ef1 (Effect.remove x ef2) in
      LetRef (x, t_e1, t_e2), (v2,ef), []
	
  | LetIn (x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      let ef1 = t_e1.info.kappa.c_effect in
      let v1 = t_e1.info.kappa.c_result_type in
      Error.check_for_not_mutable e1.info.loc v1;
      let env' = add x v1 env in
      let t_e2 = typef lab env' e2 in
      let ef2 = t_e2.info.kappa.c_effect in
      let v2 = t_e2.info.kappa.c_result_type in
      let ef = Effect.union ef1 ef2 in
      LetIn (x, t_e1, t_e2), (v2,ef), []
	    
  | If (b, e1, e2) ->
      let t_b = typef lab env b in
      expected_type b.info.loc (result_type t_b) type_v_bool;
      Error.check_no_effect b.info.loc t_b.info.kappa.c_effect;
      let t_e1 = typef lab env e1
      and t_e2 = typef lab env e2 in
      let t1 = t_e1.info.kappa.c_result_type in
      let t2 = t_e2.info.kappa.c_result_type in
      let ef = union3effects (effect t_b) (effect t_e1) (effect t_e2) in
      let v = type_v_sup loc t1 t2 in
      If (t_b, t_e1, t_e2), (v,ef), []

  | Rec (f,bl,v,var,e) ->
      let env' = check_binders (Some loc) lab env bl in
      check_type_v (Some loc) lab env' v;
      let efvar = state_var lab env' var in
      let phi0 = phi_name () in
      let tvar = typed_var loc env' var in
      (* effect for a let/rec construct is computed as a fixpoint *)
      let rec state_rec c =
	(* TODO: change label to "0" in [c] *)
	let tf = make_arrow bl c in
	let env'' = add_recursion (f,(phi0,tvar)) (add f tf env') in
	let t_e = typef initial_labels env'' e in
	if t_e.info.kappa = c then
	  t_e
      	else begin
	  if_debug_3 eprintf "%a@\n@?" print_type_c t_e.info.kappa;
	  state_rec t_e.info.kappa
      	end
      in 
      let c0 = { c_result_name = result; c_result_type = v;
		 c_effect = efvar; c_pre = []; c_post = None } in
      let t_e = state_rec c0 in
      let tf = make_arrow bl t_e.info.kappa in (* IDEM *)
      Rec (f,bl,v,var,t_e), (tf,Effect.bottom), []

  | Coerce e ->
      let te = typef lab env e in
      Coerce te, (result_type te, effect te), []

and typef_block lab env bl =
  let rec ef_block lab tyres = function
    | [] ->
	begin match tyres with
	  | Some ty -> [], ty, Effect.bottom
	  | None -> assert false
	end
    | (Assert c) :: block -> 
	let ep = state_assert lab env None c in
	let bl,t,ef = ef_block lab tyres block in
	(Assert c)::bl, t, Effect.union ep ef
    | (Label s) :: block ->
	let lab' = LabelSet.add s lab in
	let bl,t,ef = ef_block lab' tyres block in
	(Label s)::bl, t, ef
    | (Statement e) :: block ->
	let t_e = typef lab env e in
	let efe = t_e.info.kappa.c_effect in
	let t = t_e.info.kappa.c_result_type in
	let bl,t,ef = ef_block lab (Some t) block in
	(Statement t_e)::bl, t, Effect.union efe ef
  in
  ef_block lab None bl

