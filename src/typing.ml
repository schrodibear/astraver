(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.ml,v 1.19 2002-03-06 16:04:52 filliatr Exp $ i*)

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


(*s Utility functions for typing *)

let just_reads e = difference (get_reads e) (get_writes e)

let type_v_sup loc t1 t2 =
  if t1 <> t2 then Error.if_branches loc;
  t1

(* todo: type variants *)
let typed_var env (phi,r) = (phi, r, PTint)

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

let compose3effects x y z = Effect.compose x (Effect.compose y z)
      
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

let type_eq loc = function
  | PureType PTint -> Ident.t_eq_int
  | PureType PTbool -> Ident.t_eq_bool
  | PureType PTfloat -> Ident.t_eq_float
  | PureType PTunit -> Ident.t_eq_unit
  | _ -> Error.expected_type loc 
	 (fun fmt -> fprintf fmt "unit, bool, int or float")

let coerce p env k = Coerce { desc = p; info = { env = env; kappa = k } }

(*s Typing variants. 
    Return the effect i.e. variables appearing in the variant. *)

let state_var ren env (phi,r) = 
  let ids = term_vars phi in
  Idset.fold
    (fun id e ->
       if is_mutable_in_env env id then Effect.add_read id e else e)
    ids Effect.bottom 

	
(*s Typing preconditions.
    Return the effect i.e. variables appearing in the precondition. 
    Check existence of labels. *)

let state_pre lab env loc pl =
  let state e p =
    let ids = predicate_vars p.p_value in
    Idset.fold
      (fun id e ->
	 if is_mutable_in_env env id then
	   Effect.add_read id e
	 else if is_at id then begin
	   let uid,l = un_at id in
	   if not (LabelSet.mem l lab) then Error.unbound_label l loc;
	   if is_mutable_in_env env uid then
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
	     if is_mutable_in_env env id then
	       if is_write ef id then
		 Effect.add_write id e, c
	       else
		 Effect.add_read id e,
		 subst_in_predicate [id,at_id id ""] c
	     else if is_at id then begin
	       let uid,l = un_at id in
	       if l <> "" && not (LabelSet.mem l lab) then 
		 Error.unbound_label l loc;
	       if is_mutable_in_env env uid then
		 Effect.add_read uid e, c
	       else
		 e,c
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

(*s Typing programs. We infer here the type with effects. 
    [lab] is the set of labels, [env] the environment 
    and [expr] the program. *)

let rec typef lab env expr =
  let (d,(v,e),p1) = typef_desc lab env expr.info.loc expr.desc in
  let loc = Some expr.info.loc in
  let ep = state_pre lab env loc expr.info.pre in
  let (eq,q) = state_post lab env (result,v,e) loc expr.info.post in
  let e' = Effect.union e (Effect.union ep eq) in
  let p' = p1 @ expr.info.pre in
  match q, d with
    | None, Coerce expr' ->
	let c = { c_result_name = result; c_result_type = v;
		  c_effect = Effect.union e' (effect expr');
		  c_pre = p' @ (pre expr'); c_post = post expr' } in
	{ desc = expr'.desc; info = { env = env; kappa = c } }
    | _ ->
	let c = { c_result_name = result; c_result_type = v;
		  c_effect = e'; c_pre = p'; c_post = q } in
	{ desc = d; info = { env = env; kappa = c } }


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
	      
  | While (b, invopt, (var,r), bl) ->
      let efphi = state_var lab env (var,r) in
      let t_b = typef lab env b in
      Error.check_no_effect b.info.loc t_b.info.kappa.c_effect;
      let t_bl,_,ef_bl = typef_block lab env bl in
      let cb = t_b.info.kappa in
      let efinv = state_inv lab env (Some loc) invopt in
      let efb = t_b.info.kappa.c_effect in
      let ef = 
	Effect.union (Effect.union ef_bl efb) (Effect.union efinv efphi)
      in
      let v = type_v_unit in
      let var' = 
	let al = List.map (fun id -> (id,at_id id "")) (just_reads ef) in
	subst_in_term al var 
      in
      While (t_b,invopt,(var',r),t_bl), (v,ef), []
      
  | Lam ([],_) ->
      assert false

  | Lam (bl, e) ->
      let env' = traverse_binders env bl in
      let t_e = typef initial_labels env' e in
      let v = make_arrow bl t_e.info.kappa in
      let ef = Effect.bottom in
      Lam(bl,t_e), (v,ef), []

  | App ({desc=Var id} as e, Term a) when id == Ident.t_eq ->
      let t_a = typef lab env a in
      let eq = type_eq a.info.loc (result_type t_a) in
      typef_desc lab env loc (App ({e with desc = Var eq}, Term a))
      (* TODO: avoid recursive call *)
	 
  | App (f, Term a) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let t_a = typef lab env a in
      expected_type a.info.loc (result_type t_a) tx;
      let _,eapp,_,_ = decomp_kappa kapp in
      let ef = compose3effects (effect t_a) (effect t_f) eapp in
      (match t_a.desc with
	 | Expression ca when t_a.info.kappa.c_post = None ->
	     let kapp = type_c_rsubst [x,ca] kapp in
	     let (_,tapp),_,_,_ = decomp_kappa kapp in
	     (match t_f.desc with
		| Expression cf when t_f.info.kappa.c_post = None ->
		    let pl = (pre t_a) @ (pre t_f) in
		    let e = Expression (applist cf [ca]) in
		    coerce e env kapp, (tapp, ef), pl
		| _ ->	   
		    coerce (App (t_f, Term t_a)) env kapp, (tapp, ef), [])
	 | _ ->
	     let (_,tapp),_,_,_ = decomp_kappa kapp in
	     coerce (App (t_f, Term t_a)) env kapp, (tapp, ef), [])

  | App (f, (Refarg (locr,r) as a)) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let tr = type_in_env env r in
      expected_type locr tr tx;
      let kapp = type_c_subst [x,r] kapp in
      let (_,tapp),eapp,_,_ = decomp_kappa kapp in
      let ef = Effect.compose (effect t_f) eapp in
      coerce (App (t_f, a)) env kapp, (tapp, ef), []

  | App (f, Type _) ->
      failwith "todo: typing: application to a type"
      
  | LetRef (x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      let ef1 = t_e1.info.kappa.c_effect in
      let v1 = t_e1.info.kappa.c_result_type in
      let env' = add (x,Ref v1) env in
      let t_e2 = typef lab env' e2 in
      let ef2 = t_e2.info.kappa.c_effect in
      let v2 = t_e2.info.kappa.c_result_type in
      Error.check_for_let_ref loc v2;
      let ef = Effect.compose ef1 (Effect.remove ef2 x) in
      LetRef (x, t_e1, t_e2), (v2,ef), []
	
  | LetIn (x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      let ef1 = t_e1.info.kappa.c_effect in
      let v1 = t_e1.info.kappa.c_result_type in
      Error.check_for_not_mutable e1.info.loc v1;
      let env' = add (x,v1) env in
      let t_e2 = typef lab env' e2 in
      let ef2 = t_e2.info.kappa.c_effect in
      let v2 = t_e2.info.kappa.c_result_type in
      let ef = Effect.compose ef1 ef2 in
      LetIn (x, t_e1, t_e2), (v2,ef), []
	    
  | If (b, e1, e2) ->
      let t_b = typef lab env b in
      Error.check_no_effect b.info.loc t_b.info.kappa.c_effect;
      let t_e1 = typef lab env e1
      and t_e2 = typef lab env e2 in
      let efb = t_b.info.kappa.c_effect in
      let tb = t_b.info.kappa.c_result_type in
      let ef1 = t_e1.info.kappa.c_effect in
      let t1 = t_e1.info.kappa.c_result_type in
      let ef2 = t_e2.info.kappa.c_effect in
      let t2 = t_e2.info.kappa.c_result_type in
      let ef = Effect.compose efb (disj ef1 ef2) in
      let v = type_v_sup loc t1 t2 in
      If (t_b, t_e1, t_e2), (v,ef), []

  | LetRec (f,bl,v,var,e) ->
      let env' = traverse_binders env bl in
      let efvar = state_var lab env' var in
      let phi0 = phi_name () in
      let tvar = typed_var env' var in
      (* effect for a let/rec construct is computed as a fixpoint *)
      let rec state_rec c =
	let tf = make_arrow bl c in
	let env'' = add_recursion (f,(phi0,tvar)) (add (f,tf) env') in
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
      let tf = make_arrow bl t_e.info.kappa in
      LetRec (f,bl,v,var,t_e), (tf,Effect.bottom), []

  | Coerce e ->
      let te = typef lab env e in
      Coerce te, (result_type te, effect te), []

  | PPoint (s,d) -> 
      let lab' = LabelSet.add s lab in
      typef_desc lab' env loc d
	
and typef_arg lab env = function
  | Term a -> let t_a = typef lab env a in Term t_a
  | Refarg _ | Type _ as a -> a 

and typef_block lab env bl =
  let rec ef_block lab tyres = function
    | [] ->
	begin match tyres with
	    Some ty -> [],ty,Effect.bottom
	  | None -> failwith "a block should contain at least one statement"
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
	(Statement t_e)::bl, t, Effect.compose efe ef
  in
  ef_block lab None bl

let effect_app ren env f args =
  let n = List.length args in
  let tf = f.info.kappa.c_result_type in (* TODO: external function type *)
  let bl,c = match tf with
    | Arrow (bl, c) -> bl,c
    | _ -> assert false
  in
  let s,so,ok = 
    List.fold_left
    (fun (s,so,ok) (b,a) ->
       match b,a with
	 | (id,BindType (Ref _ | Array _ as v)), Refarg (_, id') ->
	     (id,id')::s, so, ok
	 | (id,BindType v), Term t ->
	     (match t.desc with
		| Expression c -> s, (id,c)::so, ok
		| _ -> s,so,false)
	 | _ -> 
	     assert false)
    ([],[],true)
    (List.combine bl args)
  in
  let c' = type_c_subst s c in
  (bl,c), (s,so,ok),
  { c' with c_result_type = type_v_rsubst so c'.c_result_type }

