
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: typing.ml,v 1.1 2001-08-17 00:52:39 filliatr Exp $ *)

open Format
open Ident
open Misc
open Util
open Logic
open Rename
open Types
open Ast
open Env 
open Effect

(*s Typing of terms. *)

let type_v_int = PureType PTint
let type_v_bool = PureType PTbool
let type_v_unit = PureType PTunit
let type_v_float = PureType PTfloat

let check_num loc t =
  if not (t = type_v_int || t = type_v_float) then
    Error.expected_type loc (fun fmt -> fprintf fmt "int or float")

let rec typing_term loc env = function
  | Tvar id -> 
      eprintf "%s@\n" (Ident.string id); flush stderr;
      (match type_in_env env id with Ref v -> v | v -> v) (* SAFE *)
  | Tconst (ConstInt _) -> type_v_int
  | Tconst (ConstBool _) -> type_v_bool
  | Tconst ConstUnit -> type_v_unit
  | Tconst (ConstFloat _) -> type_v_float
  | Tapp (id, [a;b]) when id == t_eq || id == t_noteq ->
      check_same_type loc env a b; type_v_bool
  | Tapp (id, [a;b]) 
    when id == t_add || id == t_sub || id == t_mul || id == t_div -> 
      check_two_nums loc env a b
  | Tapp (id, [a]) when id == t_neg ->
      let ta = typing_term loc env a in
      check_num loc ta; ta
  | Tapp (id, [a;b]) 
    when id == t_lt || id == t_le || id == t_gt || id == t_ge ->
      let _ = check_two_nums loc env a b in
      type_v_bool
  | Tapp (id, [Tvar a; b]) when id == access ->
      let tb = typing_term loc env b in
      if tb <> type_v_int then 
	Error.expected_type loc (fun fmt -> fprintf fmt "int");
      (match type_in_env env a with 
	 | Array (_,v) -> v 
	 | _ -> raise (Error.Error (Some loc, Error.NotAnArray a)))
  | Tapp _ ->
      failwith "todo"

and check_same_type loc env a b =
  let ta = typing_term loc env a in
  let tb = typing_term loc env b in
  if ta <> tb then Error.expected_type loc (fun fmt -> print_type_v fmt ta)

and check_two_nums loc env a b =
  let ta = typing_term loc env a in
  check_num loc ta;
  let tb = typing_term loc env b in
  if ta <> tb then Error.expected_type loc (fun fmt -> print_type_v fmt ta);
  ta

let type_of_expression ren env t =
  typing_term Loc.dummy env t

(* Ce module implante le jugement  Gamma |-a e : kappa  de la thèse.
 * Les post-conditions sont abstraites par rapport au résultat. *)

let just_reads e =
  difference (get_reads e) (get_writes e)

let type_v_sup loc t1 t2 =
  if t1 = t2 then
    t1
  else
    Error.if_branches loc

let typed_var ren env (phi,r) =
  (* TODO: type variants *)
  let a = Tvar (Ident.create "<type of variant>") in
  (phi,r,a)

(* Function application *)

(* TODO: convert is currently structural equality *)
let rec convert = function
  | (PureType c1, PureType c2) -> 
      c1 = c2
  | (Ref v1, Ref v2) -> 
      convert (v1,v2)
  | (Array (s1,v1), Array (s2,v2)) -> 
      s1 = s2 && convert (v1,v2)
  | (v1,v2) -> 
      v1 = v2
      
let effect_app ren env f args =
  let n = List.length args in
  let tf = f.info.kappa.c_result_type in (* TODO: external function type *)
  let bl,c = 
    match tf with
      | Arrow (bl, c) ->
	  if List.length bl <> n then Error.partial_app f.loc;
	  bl,c
      | _ -> Error.app_of_non_function f.loc
  in
  let check_type loc v t so =
    let v' = type_v_rsubst so v in
    if not (convert (v',t)) then 
      Error.expected_type loc (fun fmt -> print_type_v fmt v')
  in
  let s,so,ok = 
    (* s est la substitution des références, so celle des autres arg. 
     * ok nous dit si les arguments sont sans effet i.e. des expressions *)
    List.fold_left
    (fun (s,so,ok) (b,a) ->
       match b,a with
	 | (id,BindType (Ref _ | Array _ as v)), Refarg id' ->
	     let ta = type_in_env env id' in
	     check_type f.loc v ta so;
	     (id,id')::s, so, ok
	 | _, Refarg _ -> 
	     Error.should_be_a_variable f.loc
	 | (id,BindType v), Term t ->
	     let ta = t.info.kappa.c_result_type in
	     check_type t.loc v ta so;
	     (match t.desc with
		| Expression c -> s, (id,c)::so, ok
		| _ -> s,so,false)
	 | (id,BindSet), Type v ->
	     failwith "TODO"
	     (*i TODO
	     let c = Monad.trad_ml_type_v ren env v in s, (id,c)::so, ok i*)
	 | (id,BindSet), Term t -> 
	     Error.expects_a_type id t.loc
	 | (id,BindType _), Type _ -> 
	     Error.expects_a_term id
	 | (_,Untyped), _ -> 
	     assert false)
    ([],[],true)
    (List.combine bl args)
  in
  let c' = type_c_subst s c in
  (bl,c), (s,so,ok), 
  { c' with c_result_type = type_v_rsubst so c'.c_result_type }

(* Execution of a Coq AST. Returns value and type.
 * Also returns its variables *)
(*i
let state_coq_ast sign a =
  let j =
    let env = Global.env_of_context sign in
    reraise_with_loc (Ast.loc a) (judgment_of_rawconstr Evd.empty env) a in
  let ids = global_vars j.uj_val in
  j.uj_val, j.uj_type, ids
i*)

(* [is_pure p] tests wether the program p is an expression or not. *)

let rec is_pure_type_v = function
  | PureType _ -> true
  | Arrow (bl,c) -> List.for_all is_pure_arg bl && is_pure_type_c c
  | Ref _ | Array _ -> false
and is_pure_arg = function
  | (_,BindType v) -> is_pure_type_v v
  | (_,BindSet) -> true
  | (_,Untyped) -> false
and is_pure_type_c c =
  is_pure_type_v c.c_result_type && c.c_pre = [] && c.c_post = None

let rec is_pure_desc ren env = function
  | Var id -> not (is_in_env env id) || (is_pure_type_v (type_in_env env id))
  | Expression c -> 
      true (* TODO *)
      (*i (c = isevar) || (is_pure_cci (type_of_expression ren env c)) i*)
  | Acc _ -> true
  | TabAcc (_,_,p) -> is_pure ren env p
  | App (p,args) -> 
      is_pure ren env p && List.for_all (is_pure_arg ren env) args
  | SApp _ | Aff _ | TabAff _ | Seq _ | While _ | If _ 
  | Lam _ | LetRef _ | LetIn _ | LetRec _ -> false
  | Debug (_,p) -> is_pure ren env p
  | PPoint (_,d) -> is_pure_desc ren env d
and is_pure ren env p =
  p.pre = [] && p.post = None && is_pure_desc ren env p.desc
and is_pure_arg ren env = function
    Term p -> is_pure ren env p
  | Type _ -> true
  | Refarg _ -> false

(* [state_var ren env (phi,r)] returns a tuple (e,(phi',r')) 
 * where e is the effect of the variant phi and phi',r' the corresponding 
 * constr of phi and r.
 *)

let state_var ren env (phi,r) = 
  let ids = term_vars phi in
  Idset.fold
    (fun id e ->
       if is_mutable_in_env env id then Effect.add_read id e else e)
    ids Effect.bottom 
	
(* [state_pre ren env pl] returns a pair (e,c) where e is the effect of the
 * pre-conditions list pl and cl the corresponding constrs not yet abstracted
 * over the variables xi (i.e. c NOT [x1]...[xn]c !)
 *)

let state_pre ren env pl =
  let state e p =
    let ids = predicate_vars p.p_value in
    Idset.fold
      (fun id e ->
	 if is_mutable_in_env env id then
	   Effect.add_read id e
	 else if is_at id then
	   let uid,_ = un_at id in
	   if is_mutable_in_env env uid then
	     Effect.add_read uid e
	   else
	     e
	 else
	   e)
      ids e 
  in
  List.fold_left state Effect.bottom pl 

let state_assert ren env a =
  let p = pre_of_assert true a in
  state_pre ren env [p]

let state_inv ren env = function
  | None -> Effect.bottom
  | Some i -> state_assert ren env i
	  
(* [state_post ren env (id,v,ef) q] returns a pair (e,c)
 * where e is the effect of the
 * post-condition q and c the corresponding constr not yet abstracted
 * over the variables xi, yi and result.
 * Moreover the RW variables not appearing in ef have been replaced by
 * RO variables, and (id,v) is the result
 *)

let state_post ren env (id,v,ef) = function
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
	     else if is_at id then
	       let uid,_ = un_at id in
	       if is_mutable_in_env env uid then
		 Effect.add_read uid e, c
	       else
		 e,c
	     else
	       e,c)
	  ids (Effect.bottom, q.a_value)
      in
      (*i let c = abstract [id,v'] c in i*)
      ef, Some { a_name = q.a_name; a_value = c }

(* transformation of AST into constr in types V and C *)

let rec cic_type_v env ren = function
  | Ref v -> 
      Ref (cic_type_v env ren v)
  | Array (c,v) ->
      Array (c, cic_type_v env ren v)
  | Arrow (bl,c) ->
      let bl',ren',env' =
	List.fold_left
	(fun (bl,ren,env) b ->
	   let b' = cic_binder env ren b in
	   let env' = traverse_binders env [b'] in
	   let ren' = initial_renaming env' in
	   b'::bl, ren', env')
	([],ren,env) bl
      in
      let c' = cic_type_c env' ren' c in
      Arrow (List.rev bl',c')
  | PureType _ as v ->
      v

and cic_type_c env ren c =
  let id = c.c_result_name in
  let v' = cic_type_v env ren c.c_result_type in
  let efp = state_pre ren env c.c_pre in
  let e = c.c_effect in
  let efq,q' = state_post ren env (id,v',e) c.c_post in
  let ef = Effect.union e (Effect.union efp efq) in
  { c_result_name = id; c_result_type = v';
    c_effect = ef; c_pre = c.c_pre; c_post = q' }

and cic_binder env ren = function
  | (id,BindType v) ->
      let v' = cic_type_v env ren v in
      let env' = add (id,v') env in
      let ren' = initial_renaming env' in
      (id, BindType v')
  | (id,BindSet) -> (id,BindSet)
  | (id,Untyped) -> (id,Untyped)

and cic_binders env ren = function
  | [] -> []
  | b::bl ->
      let b' = cic_binder env ren b in
      let env' = traverse_binders env [b'] in
      let ren' = initial_renaming env' in
      b' :: (cic_binders env' ren' bl)


(* The case of expressions.
 * 
 * Expressions are programs without neither effects nor pre/post conditions.
 * But access to variables are allowed.
 *
 * Here we transform an expression into the corresponding term,
 * the variables still appearing as VAR (they will be abstracted in
 * Mlise.trad)
 * We collect the pre-conditions (e<N for t[e]) as we traverse the term.
 * We also return the effect, which does contain only *read* variables.
 *)

let states_expression ren env expr =
  let rec effect pl = function
    | Var id -> 
	Tvar id, pl, Effect.bottom
    | Expression c -> 
	(* TODO: division by zero => obligation *)
	c, pl, Effect.bottom
    | Acc id -> 
	Tvar id, pl, Effect.add_read id Effect.bottom
    | TabAcc (_,id,p) ->
	let c,pl,ef = effect pl p.desc in
	let pre = make_pre_access ren env id c in
	make_raw_access ren env (id,id) c, 
	(anonymous_pre true pre)::pl, Effect.add_read id ef
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
		     (*i let v' = cic_type_v env ren v in
		     (Monad.trad_ml_type_v ren env v')::l, pl, e i*)
		 | Refarg _ -> 
		     assert false) 
	    args ([],pl,e) 
	in
	Error.check_for_non_constant p.loc a;
	applist a args, pl, e
    | _ -> 
	assert false
  in
  let e0 = state_pre ren env expr.pre in
  let c,pl,e = effect [] expr.desc in
  let v = typing_term expr.loc env c in
  let ef = Effect.union e0 e in
  Expression c, (v,ef), expr.pre @ pl


(* We infer here the type with effects.
 * The type of types with effects (ml_type_c) is defined in the module ProgAst.
 * 
 * A program of the shape {P} e {Q} has a type 
 *   
 *        V, E, {None|Some P}, {None|Some Q}
 *
 * where - V is the type of e
 *       - E = (I,O) is the effect; the input I contains
 *         all the input variables appearing in P,e and Q;
 *         the output O contains variables possibly modified in e
 *       - P is NOT abstracted
 *       - Q = [y'1]...[y'k][result]Q where O = {y'j}
 *         i.e. Q is only abstracted over the output and the result
 *         the other variables now refer to value BEFORE
 *)

let verbose_fix = ref false

let rec states_desc ren env loc = function
	
  | Expression c ->
      let v = typing_term loc env c in
      Expression c, (v,Effect.bottom)

  | Acc _ ->
      failwith "Typing.states: term is supposed not to be pure"

  | Var id ->
      let v = type_in_env env id in
      let ef = Effect.bottom in
      Var id, (v,ef)

  | Aff (x, e1) ->
      Error.check_for_reference loc x (type_in_env env x);
      let s_e1 = states ren env e1 in
      let e = s_e1.info.kappa.c_effect in
      let ef = add_write x e in
      let v = type_v_unit in
      Aff (x, s_e1), (v, ef)

  | TabAcc (check, x, e) ->
      let s_e = states ren env e in
      let efe = s_e.info.kappa.c_effect in
      let ef = Effect.add_read x efe in
      let _,ty = dearray_type (type_in_env env x) in
      TabAcc (check, x, s_e), (ty, ef)

  | TabAff (check, x, e1, e2) ->
      let s_e1 = states ren env e1 in
      let s_e2 = states ren env e2 in 
      let ef1 = s_e1.info.kappa.c_effect in
      let ef2 = s_e2.info.kappa.c_effect in
      let ef = Effect.add_write x (Effect.union ef1 ef2) in
      let v = type_v_unit in
      TabAff (check, x, s_e1, s_e2), (v,ef)

  | Seq bl ->
      let bl,v,ef,_ = states_block ren env bl in
      Seq bl, (v,ef)
	      
  | While(b, invopt, (var,r), bl) ->
      let efphi = state_var ren env (var,r) in
      let ren' = next ren [] in
      let s_b = states ren' env b in
      let s_bl,_,ef_bl,_ = states_block ren' env bl in
      let cb = s_b.info.kappa in
      let efinv = state_inv ren env invopt in
      let efb = s_b.info.kappa.c_effect in
      let ef = 
	Effect.union (Effect.union ef_bl efb) (Effect.union efinv efphi)
      in
      let v = type_v_unit in
      let var' = 
	let al = List.map (fun id -> (id,at_id id "")) (just_reads ef) in
	subst_in_term al var 
      in
      While (s_b,invopt,(var',r),s_bl), (v,ef)
      
  | Lam ([],_) ->
      failwith "Typing.states: abs. should have almost one binder"

  | Lam (bl, e) ->
      let bl' = cic_binders env ren bl in
      let env' = traverse_binders env bl' in
      let ren' = initial_renaming env' in
      let s_e = states ren' env' e in
      let v = make_arrow bl' s_e.info.kappa in
      let ef = Effect.bottom in
      Lam(bl',s_e), (v,ef)
	 
  (* Connectives AND and OR *)
  | SApp ([Var id], [e1;e2]) ->
      let s_e1 = states ren env e1
      and s_e2 = states ren env e2 in
      let ef1 = s_e1.info.kappa.c_effect
      and ef2 = s_e2.info.kappa.c_effect in
      let ef = Effect.union ef1 ef2 in
      SApp ([Var id], [s_e1; s_e2]), (type_v_bool, ef)

  (* Connective NOT *)
  | SApp ([Var id], [e]) ->
      let s_e = states ren env e in
      let ef = s_e.info.kappa.c_effect in
      SApp ([Var id], [s_e]), (type_v_bool, ef)
      
  | SApp _ -> invalid_arg "Typing.states (SApp)"

  (* ATTENTION:
     Si un argument réel de type ref. correspond à une ref. globale
     modifiée par la fonction alors la traduction ne sera pas correcte.
     Exemple:
            f=[x:ref Int]( r := !r+1 ; x := !x+1) modifie r et son argument x
            donc si on l'applique à r justement, elle ne modifiera que r
            mais le séquencement ne sera pas correct. *)

  | App (f, args) ->
      let s_f = states ren env f in
      let eff = s_f.info.kappa.c_effect in
      let s_args = List.map (states_arg ren env) args in
      let ef_args = 
	List.map 
	  (function Term t -> t.info.kappa.c_effect 
	          | _ -> Effect.bottom) 
	  s_args 
      in
      let _,_,capp = effect_app ren env s_f s_args in
      let tapp = capp.c_result_type in
      let efapp = capp.c_effect in
      let ef = 
	Effect.compose (List.fold_left Effect.compose eff ef_args) efapp
      in
      App (s_f, s_args), (tapp, ef)
      
  | LetRef (x, e1, e2) ->
      let s_e1 = states ren env e1 in
      let ef1 = s_e1.info.kappa.c_effect in
      let v1 = s_e1.info.kappa.c_result_type in
      let env' = add (x,Ref v1) env in
      let ren' = next ren [x] in
      let s_e2 = states ren' env' e2 in
      let ef2 = s_e2.info.kappa.c_effect in
      let v2 = s_e2.info.kappa.c_result_type in
      Error.check_for_let_ref loc v2;
      let ef = Effect.compose ef1 (Effect.remove ef2 x) in
      LetRef (x, s_e1, s_e2), (v2,ef)
	
  | LetIn (x, e1, e2) ->
      let s_e1 = states ren env e1 in
      let ef1 = s_e1.info.kappa.c_effect in
      let v1 = s_e1.info.kappa.c_result_type in
      Error.check_for_not_mutable e1.loc v1;
      let env' = add (x,v1) env in
      let s_e2 = states ren env' e2 in
      let ef2 = s_e2.info.kappa.c_effect in
      let v2 = s_e2.info.kappa.c_result_type in
      let ef = Effect.compose ef1 ef2 in
      LetIn (x, s_e1, s_e2), (v2,ef)
	    
  | If (b, e1, e2) ->
      let s_b = states ren env b in
      let s_e1 = states ren env e1
      and s_e2 = states ren env e2 in
      let efb = s_b.info.kappa.c_effect in
      let tb = s_b.info.kappa.c_result_type in
      let ef1 = s_e1.info.kappa.c_effect in
      let t1 = s_e1.info.kappa.c_result_type in
      let ef2 = s_e2.info.kappa.c_effect in
      let t2 = s_e2.info.kappa.c_result_type in
      let ef = Effect.compose efb (disj ef1 ef2) in
      let v = type_v_sup loc t1 t2 in
      If (s_b, s_e1, s_e2), (v,ef)

  | LetRec (f,bl,v,var,e) ->
      let bl' = cic_binders env ren bl in
      let env' = traverse_binders env bl' in
      let ren' = initial_renaming env' in
      let v' = cic_type_v env' ren' v in
      let efvar = state_var ren' env' var in
      let phi0 = phi_name () in
      let tvar = typed_var ren env' var in
      (* effect for a let/rec construct is computed as a fixpoint *)
      let rec state_rec c =
	let tf = make_arrow bl' c in
	let env'' = add_recursion (f,(phi0,tvar)) (add (f,tf) env') in
	let s_e = states ren' env'' e in
	if s_e.info.kappa = c then
	  s_e
      	else begin
	  if !verbose_fix then print_type_c err_formatter s_e.info.kappa;
	  state_rec s_e.info.kappa
      	end
      in 
      let c0 = { c_result_name = result; c_result_type = v';
		 c_effect = efvar; c_pre = []; c_post = None } in
      let s_e = state_rec c0 in
      let tf = make_arrow bl' s_e.info.kappa in
      LetRec (f,bl',v',var,s_e), (tf,Effect.bottom)

  | PPoint (s,d) -> 
      let ren' = push_date ren s in
      states_desc ren' env loc d
	
  | Debug _ -> failwith "Typing.states: Debug: TODO"


and states_arg ren env = function
  | Term a    -> let s_a = states ren env a in Term s_a
  | Refarg id -> Refarg id
  | Type v    -> let v' = cic_type_v env ren v in Type v'
	

and states ren env expr =
  (* Here we deal with the pre- and post- conditions:
   * we add their effects to the effects of the program *)
  let (d,(v,e),p1) = 
    if is_pure_desc ren env expr.desc then
      states_expression ren env expr
    else
      let (d,ve) = states_desc ren env expr.loc expr.desc in (d,ve,[])
  in
  let ep = state_pre ren env expr.pre in
  let (eq,q) = state_post ren env (result,v,e) expr.post in
  let e' = Effect.union e (Effect.union ep eq) in
  let p' = p1 @ expr.pre in
  let c = { c_result_name = result; c_result_type = v;
	    c_effect = e'; c_pre = p'; c_post = q } in
  let tinfo = { env = env; kappa = c } in
  { desc = d;
    loc = expr.loc;
    pre = p'; post = q; (* on les conserve aussi ici pour prog_wp *)
    info = tinfo }


and states_block ren env bl =
  let rec ef_block ren tyres = function
    | [] ->
	begin match tyres with
	    Some ty -> [],ty,Effect.bottom,ren
	  | None -> failwith "a block should contain at least one statement"
	end
    | (Assert c) :: block -> 
	let ep = state_assert ren env c in
	let bl,t,ef,ren' = ef_block ren tyres block in
	(Assert c)::bl, t, Effect.union ep ef, ren'
    | (Label s) :: block ->
	let ren' = push_date ren s in
	let bl,t,ef,ren'' = ef_block ren' tyres block in
	(Label s)::bl, t, ef, ren''
    | (Statement e) :: block ->
	let s_e = states ren env e in
	let efe = s_e.info.kappa.c_effect in
	let t = s_e.info.kappa.c_result_type in
	let ren' = next ren (get_writes efe) in
	let bl,t,ef,ren'' = ef_block ren' (Some t) block in
	(Statement s_e)::bl, t, Effect.compose efe ef, ren''
  in
  ef_block ren None bl

