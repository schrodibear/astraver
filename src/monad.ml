(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: monad.ml,v 1.36 2002-06-21 15:20:24 filliatr Exp $ i*)

open Format
open Ident
open Misc
open Util
open Logic
open Types
open Ast
open Rename
open Effect
open Env

(*s [product ren [y1,z1;...;yk,zk] q] constructs the (possibly dependent) 
    tuple type
 
       $z1 \times ... \times zk$ if no postcondition
    or $\exists. y1:z1. ... yk:zk. (Q x1 ... xn)$  otherwise *)
 
let product before ren env w q = match q,w with
  | None, [_,v] -> 
      v
  | None, _ -> 
      TTtuple (w, None)
  | Some q, _ -> 
      TTtuple (w, Some (TTpred (apply_post before ren env q).a_value))


(*s [arrow_pred ren v pl] abstracts the term [v] over the pre-condition if any
    i.e. computes
 
      (P1 x1 ... xn) -> ... -> (Pk x1 ... xn) -> v
  
    where the [xi] are given by the renaming [ren]. *)

let arrow_pred ren env v pl = 
  List.fold_right
    (fun p t -> 
       if p.p_assert then 
	 t
       else 
	 let p = apply_pre ren env p in
	 TTarrow ((id_of_name p.p_name, CC_pred_binder p.p_value), t))
    pl v
	
let arrow_vars = 
  List.fold_right (fun (id,v) t -> TTarrow ((id, CC_var_binder v), t))


(*s Translation of effects types in CC types.
  
    [trad_type_v] and [trad_type_c] translate types with effects
    into CC types. *)

let rec trad_type_c ren env k = 
  let ((_,v),e,p,q) = decomp_kappa k in
  let i,o = get_repr e in
  let before = label_name () in
  let ren' = next (push_date ren before) o in
  let lo = output ren' env (v,o) in
  let ty = product before ren' env lo q in
  let ty = arrow_pred ren env ty p in
  let li = input ren env i in
  arrow_vars li ty

and trad_type_v ren env = function
  | Ref _ 
  | Array _ -> 
      assert false
  | Arrow (bl, c) ->  
      let bl',ren',env' =
	List.fold_left
	  (fun (bl,ren,env) b -> match b with
	     | (id, BindType ((Ref _ | Array _) as v)) ->
		 let env' = Env.add id v env in
		 let ren' = initial_renaming env' in
		 (bl, ren', env')
	     | (id, BindType v) -> 
		 let tt = trad_type_v ren env v in
		 let env' = Env.add id v env in
		 let ren' = initial_renaming env' in
		 (id,tt)::bl, ren', env'
	     | _ -> 
		 failwith "Monad: trad_type_v: not yet implemented")
 	  ([],ren,env) bl 
      in
      arrow_vars (List.rev bl') (trad_type_c ren' env' c)
  | PureType c ->
      TTpure c

and input ren env i =
  prod ren env i

and output ren env (v,o) =
  let tv = trad_type_v ren env v in
  (prod ren env o) @ [result,tv]

and input_output ren env c =
  let ((_,v),e,_,_) = decomp_kappa c in
  let i,o = get_repr e in
  input ren env i, output ren env (v,o)

and prod ren env g = 
  List.map (fun id -> (current_var ren id, trad_type_in_env ren env id)) g

and trad_imp_type ren env = function
  | Ref v -> trad_type_v ren env v
  | Array (t, v) -> TTarray (t, trad_type_v ren env v)
  | _ -> assert false

and trad_type_in_env ren env id =
  let v = type_in_env env id in 
  trad_imp_type ren env v


(*s The Monadic operators. They are operating on values of the following
    type [interp] (functions producing a [cc_term] when given a renaming
    data structure). *)

type interp = Rename.t -> predicate cc_term


(*s [unit k t ren env] constructs the tuple 
  
      (y1, ..., yn, t, ?::(q/ren y1 ... yn t))
  
    where the [yi] are the values of the output of [k].
   If there is no [yi] and no postcondition, it is simplified into 
   [t] itself. *)

let lambda_vars =
  List.fold_right (fun (id,v) t -> TTlambda ((id, CC_var_binder v), t))

let unit info t ren = 
  let env = info.env in
  let t = apply_term ren env t in
  let k = info.kappa in
  let ef = k.c_effect in
  let q = k.c_post in
  let ids = get_writes ef in
  if ids = [] && q = None then
    CC_term t
  else 
    let hole, holet = match q with
      | None -> 
	  [], None
      | Some c -> 
	  let h = 
	    let c = apply_post info.label ren env c in
	    tsubst_in_predicate (subst_one result t) c.a_value
	  in
	  let ht = 
	    let _,o = get_repr ef in
	    let ren' = Rename.next ren (result :: o) in
	    let result' = current_var ren' result in
	    let bl = 
	      List.map (fun id -> (current_var ren' id, 
				   trad_type_in_env ren env id)) o @
	      [result', trad_type_v ren env k.c_result_type]
	    in
	    let c = apply_post info.label ren' env c in
	    let c = subst_in_predicate (subst_onev result result') c.a_value in
	    lambda_vars bl (TTpred c)
	  in
	  [ CC_hole h ], Some ht
    in
    CC_tuple (
      (List.map (fun id -> let id' = current_var ren id in CC_var id') ids) @
      (CC_term t) :: hole,
      holet)

(*s [compose k1 e1 e2 ren env] constructs the term
   
        [ let h1 = ?:P1 in ... let hn = ?:Pm in ]
          let y1,y2,...,yn, res1 [,q] = <e1 ren> in
          <e2 res1 ren'>

    where [ren' = next w1 ren] and [y1,...,yn = w1/ren] *)

let binding_of_alist ren env =
  List.map
    (fun (id,id') -> (id', CC_var_binder (trad_type_in_env ren env id)))

let make_pre env ren p = 
  let p = apply_pre ren env p in
  pre_name p.p_name, p.p_value

let let_pre (id, h) cc = 
  CC_letin (false, [id, CC_pred_binder h], CC_hole h, cc)

let let_many_pre = List.fold_right let_pre

let gen_compose isapp info1 e1 e2 ren =
  let env = info1.env in
  let k1 = info1.kappa in
  let (res1,v1),ef1,p1,q1 = decomp_kappa k1 in
  let ren = push_date ren info1.label in
  let r1,w1 = get_repr ef1 in
  let ren' = next ren w1 in
  let res1,ren' = fresh ren' res1 in
  let tt1 = trad_type_v ren env v1 in
  let b = [res1, CC_var_binder tt1] in
  let b',dep = match q1 with
    | None -> 
	[], false
    | Some q1 -> 
	let q1 = apply_post info1.label ren' env q1 in
	let hyp = subst_in_predicate (subst_onev result res1) q1.a_value in
	[post_name q1.a_name, CC_pred_binder hyp], true 
  in
  let vo = current_vars ren' w1 in
  let bl = (binding_of_alist ren env vo) @ b @ b' in
  let pre1 = List.map (make_pre env ren) p1 in
  let cc1 = 
    if isapp then 
      let input = List.map (fun (_,id') -> CC_var id') (current_vars ren r1) in
      let inputpre = List.map (fun (id,_) -> CC_var id) pre1 in
      cc_applist (e1 ren) (input @ inputpre)
    else 
      e1 ren 
  in
  let cc = CC_letin (dep, bl, cc1, e2 res1 ren') in
  let_many_pre pre1 cc

let compose = gen_compose false
let apply = gen_compose true

(*s [cross_label] is an operator to be used when a label is encountered *)

let cross_label l e ren = e (push_date ren l)

(*s Inserting assertions *)

let insert_pre env p t ren = 
  let_pre (make_pre env ren p) (t ren)

let insert_many_pre env pl t =
  List.fold_left (fun t h -> insert_pre env h t) t pl

(*s [abstraction env k e] abstracts a term [e] with respect to the 
    list of read variables, to the preconditions/assertions, i.e.
    builds

      [x1]...[xk][h1:P1]...[hn:Pn]let h'1 = ?:P'1 in ... let H'm = ?:P'm in t
    *)

let make_abs bl t = match bl with
  | [] -> t
  | _  -> cc_lam bl t

let bind_pre ren env p =
  pre_name p.p_name, CC_pred_binder (apply_pre ren env p).p_value

let abs_pre env pl t =
  List.fold_right
    (fun p t ->
       if p.p_assert then
	 insert_pre env p t
       else
	 (fun ren -> CC_lam (bind_pre ren env p, t ren)))
    pl t

let abstraction info e ren =
  let env = info.env in
  let k = info.kappa in
  let _,ef,p,_ = decomp_kappa k in
  let ids = get_reads ef in
  let al = current_vars ren ids in
  let c = abs_pre env p e ren in
  let bl = binding_of_alist ren env al in
  make_abs bl c

let fresh id e ren =
  let id',ren' = Rename.fresh ren id in
  e id' ren'

(*s Well-founded recursion. 

    \begin{verbatim}
    (well_founded_induction
       A R ?::(well_founded A R)
       [Phi:A] (bl) (x) Phi=phi(x) -> <info>
       [Phi:A][w:(Phi0:A) Phi0<Phi -> (bl) (x) Phi=phi(x) -> <info>]
         [bl][x][eq:Phi=phi(x)][h:<pre info>]

            <body where w <- (w phi(x1) ?::phi(x1)<Phi 
                              argl x1 ?::phi(x1)=phi(x1) ?::<pre info>)>

       phi(x) bl x ?::phi(x)=phi(x) ?::<pre info>)
    \end{verbatim}
*)

let wfrec_with_binders bl (phi,a,r) info f ren =
  let env = info.env in
  let vphi = variant_name () in
  let wr = get_writes info.kappa.c_effect in
  let info' = 
    let eq = anonymous_pre false (equality (Tvar vphi) phi) in
    { info with kappa = { info.kappa with c_pre = eq :: info.kappa.c_pre }}
  in
  let a = TTpure a in
  let w = wf_name () in
  let k = info'.kappa in
  let ren' = next ren (get_writes k.c_effect) in 
  let tphi = tt_arrow bl (trad_type_c ren' env k) in
  let vphi0 = variant_name () in
  let tphi0 = 
    let k0 = type_c_subst (subst_onev vphi vphi0) k in 
    tt_arrow bl (trad_type_c ren' env k0) 
  in
  let input ren =
    let input = List.map (fun (_,id') -> CC_var id') (current_vars ren wr) in
    let pl = (anonymous_pre false (equality phi phi)) :: info.kappa.c_pre in
    let holes = List.map (fun p -> CC_hole (apply_pre ren env p).p_value) pl in
    input @ holes
  in
  let tw = 
    let r_phi0_phi = predicate_of_term (applist r [Tvar vphi0; Tvar vphi]) in
    TTarrow ((vphi0, CC_var_binder a),
	     TTarrow ((pre_name Anonymous, CC_pred_binder r_phi0_phi), tphi0))
  in
  let fw ren = 
    let tphi = apply_term ren env phi in
    let decphi = predicate_of_term (applist r [tphi; Tvar vphi]) in
    cc_applist (CC_var w) ([CC_term tphi; CC_hole decphi] @ input ren) 
  in
  cc_applist (CC_var well_founded_induction)
    ([CC_type a; CC_term r;
      CC_hole (papplist (Pvar well_founded) [r]);
      CC_type (TTlambda ((vphi, CC_var_binder a), tphi));
      cc_lam 
	([vphi, CC_var_binder a; w, CC_var_binder tw] @ bl)
	(abstraction info' (f fw) ren');
      CC_term (apply_term ren env phi)] @
     input ren)

let wfrec = wfrec_with_binders []


(*s Interpretations of recursive functions are stored in the following
    table. *)

let rec_table = Hashtbl.create 97

let is_rec = Hashtbl.mem rec_table
let find_rec = Hashtbl.find rec_table

let with_rec f tf e ren = 
  Hashtbl.add rec_table f tf; 
  let r = e ren in 
  Hashtbl.remove rec_table f; 
  r

