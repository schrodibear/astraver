(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.ml,v 1.13 2002-03-01 16:29:49 filliatr Exp $ i*)

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

(*i***
let check_num loc a t =
  if not (t = type_v_int || t = type_v_float) then
    Error.term_expected_type loc 
      (fun fmt -> print_term fmt a) (fun fmt -> fprintf fmt "int or float")
***i*)

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
(*i***
  | Tapp (id, [a;b]) when is_arith id ->
      check_two_nums loc env a b
  | Tapp (id, [a]) when id == t_neg ->
      let ta = typing_term loc env a in
      check_num loc a ta; ta
  | Tapp (id, [a;b]) when is_comparison id ->
      let _ = check_two_nums loc env a b in
      type_v_bool
  | Tapp (id, [Tvar a; b]) when id == access ->
      let tb = typing_term loc env b in
      if tb <> type_v_int then 
	Error.term_expected_type loc 
	  (fun fmt -> print_term fmt b) (fun fmt -> fprintf fmt "int");
      (match type_in_env env a with 
	 | Array (_,v) -> v 
	 | _ -> raise (Error.Error (Some loc, Error.NotAnArray a)))
  | Tapp (id, [a]) when id == t_sqrt ->
      let ta = typing_term loc env a in
      if ta <> type_v_float then
	Error.term_expected_type loc 
	  (fun fmt -> print_term fmt a) (fun fmt -> fprintf fmt "float");
      type_v_float
***i*)

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


(*i***
and check_two_nums loc env a b =
  let ta = typing_term loc env a in
  check_num loc a ta;
  let tb = typing_term loc env b in
  if ta <> tb then 
    Error.term_expected_type loc 
      (fun fmt -> print_term fmt b) (fun fmt -> print_type_v fmt ta);
  ta
***i*)

let type_of_expression ren env t = typing_term Loc.dummy env t


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

let effect p = p.info.kappa.c_effect
let pre p = p.info.kappa.c_pre
let post p = p.info.kappa.c_post
let result_type p = p.info.kappa.c_result_type

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
      (*i let c = abstract [id,v'] c in i*)
      ef, Some { a_name = q.a_name; a_value = c }


(*s Detection and typing of pure expressions.
  
    Pure expressions are programs without neither effects nor 
    pre/post-conditions, but access to variables and arrays are allowed.

    We collect the preconditions for array access([e<N] for [t[e]])
    as we traverse the term. *)

(* [is_pure p] tests wether the program [p] is an expression or not. *)

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

let rec is_pure env p =
  p.info.pre = [] && p.info.post = None && is_pure_desc env p.desc
and is_pure_desc env = function
  | Var id -> not (is_in_env env id) || (is_pure_type_v (type_in_env env id))
  | Acc id -> is_pure_type_v (deref_type (type_in_env env id))
  | Expression _ -> true
  | TabAcc (_,_,p) -> is_pure env p
  | App (e1,e2) -> is_pure env e1 && is_pure_arg env e2
  | Aff _ | TabAff _ | Seq _ | While _ | If _ 
  | Lam _ | LetRef _ | LetIn _ | LetRec _ -> false
  | Debug (_,p) -> is_pure env p
  | PPoint (_,d) -> is_pure_desc env d
and is_pure_arg env = function
  | Term p -> is_pure env p
  | Type _ -> true
  | Refarg _ -> false

let partial_pre = function
  | Tapp (id, [a;b]) when id == t_div ->
      let p = neq b (Tconst (ConstInt 0)) in
      [anonymous_pre true p]
  | Tapp (id, [a]) when id == t_sqrt ->
      let p = ge a (Tconst (ConstInt 0)) in
      [anonymous_pre true p]
  | _ ->
      []

(*i***
let typef_expression lab env expr =
  let rec effect pl = function
    | Var id -> 
	Tvar id, pl, Effect.bottom
    | Expression c -> 
	c, pl, Effect.bottom
    | Acc id -> 
	Tvar id, pl, Effect.add_read id Effect.bottom
    | TabAcc (_,id,p) ->
	let c,pl,ef = effect pl p.desc in
	let pre = make_pre_access env id c in
	make_raw_access env (id,id) c, 
	(anonymous_pre true pre) :: pl, Effect.add_read id ef
    | App (p,args) ->
	let a,pl,e = effect pl p.desc in
	let args,pl,e =
	  List.fold_right
	    (fun arg (l,pl,e) -> 
	       match arg with
		 | Term p ->
		     let carg,pl,earg = effect pl p.desc in
		     carg::l, pl, Effect.union e earg
		 | Type v ->
		     failwith "TODO"
		 | Refarg _ -> 
		     assert false) 
	    args ([],pl,e) 
	in
	Error.check_for_non_constant p.info.loc a;
	let t = applist a args in
	t, (partial_pre t) @ pl, e
    | _ -> 
	assert false
  in
  let e0 = state_pre lab env (Some expr.info.loc) expr.info.pre in
  let c,pl,e = effect [] expr.desc in
  let v = typing_term expr.info.loc env c in
  let ef = Effect.union e0 e in
  Expression c, (v,ef), expr.info.pre @ pl
***i*)

(*s Typing programs. We infer here the type with effects. 
    [lab] is the set of labels, [env] the environment 
    and [expr] the program. *)

let rec typef lab env expr =
  let (d,(v,e),p1) = typef_desc lab env expr.info.loc expr.desc in
(*i***
    if is_pure_desc env expr.desc then
      typef_expression lab env expr
    else
***i*)
  let loc = Some expr.info.loc in
  let ep = state_pre lab env loc expr.info.pre in
  let (eq,q) = state_post lab env (result,v,e) loc expr.info.post in
  let e' = Effect.union e (Effect.union ep eq) in
  let p' = p1 @ expr.info.pre in
  let c = { c_result_name = result; c_result_type = v;
	    c_effect = e'; c_pre = p'; c_post = q } in
  let tinfo = { env = env; kappa = c } in
  { desc = d; info = tinfo }


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
	 
  | App (f, Term a) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let (_,tapp),eapp,_,_ = decomp_kappa kapp in
      let t_a = typef lab env a in
      expected_type a.info.loc (result_type t_a) tx;
      let ef = compose3effects (effect t_a) (effect t_f) eapp in
      (match t_a.desc with
	 | Expression ca when t_a.info.kappa.c_post = None ->
	     let tapp' = type_v_rsubst [x,ca] tapp in
	     (match t_f.desc with
		| Expression cf when t_f.info.kappa.c_post = None ->
		    let pl = (pre t_a) @ (pre t_f) in
		    Expression (applist cf [ca]), (tapp', ef), pl
		| _ ->	   
		    App (t_f, Term t_a), (tapp', ef), [])
	 | _ ->
	     App (t_f, Term t_a), (tapp, ef), [])

  | App (f, (Refarg (locr,r) as a)) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let (_,tapp),eapp,_,_ = decomp_kappa kapp in
      let tr = type_in_env env r in
      expected_type locr tr tx;
      let ef = Effect.compose (effect t_f) eapp in
      let tapp' = type_v_subst [x,r] tapp in
      App (t_f, a), (tapp', ef), []

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
      (* let bl' = cic_binders env ren bl in *)
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

  | PPoint (s,d) -> 
      let lab' = LabelSet.add s lab in
      typef_desc lab' env loc d
	
  | Debug _ -> failwith "Typing.typef: Debug: TODO"


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


and typef_app ren env f args =
  let floc = f.info.loc in
  let argsloc = List.map arg_loc args in
  let t_f = typef ren env f in
  let t_args = List.map (typef_arg ren env) args in
  let n = List.length args in
  let tf = t_f.info.kappa.c_result_type in (* TODO: external function type *)
  let bl,c = 
    match tf with
      | Arrow (bl, c) ->
	  if List.length bl <> n then Error.partial_app floc;
	  bl,c
      | _ -> 
	  Error.app_of_non_function floc
  in
  let check_type loc v t so =
    let v' = type_v_rsubst so v in
    if not (subtype (v',t)) then 
      Error.ill_typed_argument loc (fun fmt -> print_type_v fmt v')
  in
  let s,so,ok = 
    (* [s] is the references substitution, [so] other args substitution. *)
    (* [ok] means arguments are side-effects free i.e. expressions *)
    List.fold_left
    (fun (s,so,ok) (b,a,tloc) ->
       match b,a with
	 | (id,BindType (Ref _ | Array _ as v)), Refarg (loc, id') ->
	     let ta = type_in_env env id' in
	     check_type loc v ta so;
	     (id,id')::s, so, ok
	 | (id,_), Refarg (loc,_) -> 
	     Error.should_not_be_a_reference loc
	 | (id,BindType v), Term t ->
	     let ta = t.info.kappa.c_result_type in
	     check_type tloc v ta so;
	     (match t.desc with
		| Expression c -> s, (id,c)::so, ok
		| _ -> s,so,false)
	 | (id,BindSet), Type v ->
	     failwith "TODO"
	     (*i TODO
	     let c = Monad.trad_ml_type_v ren env v in s, (id,c)::so, ok i*)
	 | (id,BindSet), Term t -> 
	     Error.expects_a_type id tloc
	 | (id,BindType _), Type _ -> 
	     Error.expects_a_term id
	 | (_,Untyped), _ -> 
	     assert false)
    ([],[],true)
    (list_combine3 bl t_args argsloc)
  in
  let c' = type_c_subst s c in
  t_f, t_args, (*i (bl,c), (s,so,ok), i*)
  { c' with c_result_type = type_v_rsubst so c'.c_result_type }


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

