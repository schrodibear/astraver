(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: monad.ml,v 1.9 2002-03-13 10:01:37 filliatr Exp $ i*)

open Format
open Ident
open Misc
open Util
open Logic
open Types
open Ast
open Rename
open Env
open Effect

(*s [product ren [y1,z1;...;yk,zk] q] constructs the (possibly dependent) 
    tuple type
 
       $z1 \times ... \times zk$ if no postcondition
    or $\exists. y1:z1. ... yk:zk. (Q x1 ... xn)$  otherwise *)
 
let product ren env w q = match q,w with
  | None, [_,v] -> v
  | None, _ -> TTtuple (w, None)
  | Some q, _ -> TTtuple (w, Some (apply_post ren env q).a_value)


(*s [arrow_pred ren v pl] abstracts the term [v] over the pre-condition if any
    i.e. computes
 
      (P1 x1 ... xn) -> ... -> (Pk x1 ... xn) -> v
  
    where the [xi] are given by the renaming [ren]. *)

let arrow_pred ren env v pl = 
  List.fold_left 
    (fun t p -> 
       if p.p_assert then 
	 t
       else 
	 let p = apply_pre ren env p in
	 TTarrow ((id_of_name p.p_name, CC_pred_binder p.p_value), t))
    v pl
	
let arrow_vars = 
  List.fold_left (fun t (id,v) -> TTarrow ((id, CC_var_binder v), t))


(*s Translation of effects types in CC types.
  
    [trad_ml_type_v] and [trad_ml_type_c] translate types with effects
    into CC types. *)

let rec trad_ml_type_c ren env k = 
  let ((res,v),e,p,q) = decomp_kappa k in
  let lo = output ren env ((res,v),e) in
  let ty = product ren env lo q in
  let ty = arrow_pred ren env ty p in
  let li = input ren env e in
  arrow_vars ty li

and trad_ml_type_v ren env = function
  | Ref _ 
  | Array _ -> 
      assert false
  | Arrow (bl, c) ->
      let bl',ren',env' =
	List.fold_left
	  (fun (bl,ren,env) b -> match b with
	     | (id, BindType ((Ref _ | Array _) as v)) ->
		 let env' = add (id,v) env in
		 let ren' = initial_renaming env' in
		 (bl, ren', env')
	     | (id, BindType v) -> 
		 let tt = trad_ml_type_v ren env v in
		 let env' = add (id,v) env in
		 let ren' = initial_renaming env' in
		 (id,tt)::bl, ren', env'
	     | _ -> failwith "Monad: trad_ml_type_v: not yet implemented"
 	  )
 	  ([],ren,env) bl 
      in
      arrow_vars (trad_ml_type_c ren' env' c) bl'
  | PureType c ->
      TTpure c

and input ren env e  =
  let i,_ = Effect.get_repr e in
  prod ren env i

and output ren env ((id,v),e) =
  let tv = trad_ml_type_v ren env v in
  let _,o = Effect.get_repr e in
  (prod ren env o) @ [id,tv]

and input_output ren env c =
  let ((res,v),e,_,_) = decomp_kappa c in
  input ren env e, output ren env ((res,v),e)

and prod ren env g = 
  List.map (fun id -> (current_var ren id, trad_type_in_env ren env id)) g

and trad_imp_type ren env = function
  | Ref v -> trad_ml_type_v ren env v
  | Array (t, v) -> TTarray (t, trad_ml_type_v ren env v)
  | _ -> assert false

and trad_type_in_env ren env id =
  let v = type_in_env env id in 
  trad_imp_type ren env v


(*s The Monadic operators. They are operating on values of the following
    type [interp] (functions producing a [cc_term] when given a renaming
    data structure). *)

type interp = Rename.t -> cc_term


(*s [unit k t ren env] constructs the tuple 
  
      (y1, ..., yn, t, ?::(q/ren y1 ... yn t))
  
    where the [yi] are the values of the output of [k].
   If there is no [yi] and no postcondition, it is simplified into 
   [t] itself. *)

let unit info t ren = 
  let env = info.env in
  let t = apply_term ren env t in
  let k = info.kappa in
  let ef = k.c_effect in
  let q = k.c_post in
  let ids = get_writes ef in
  if ids = [] && q = None then
    CC_expr t
  else 
    let hole = match q with
      | None -> 
	  []
      | Some c -> 
	  let c = apply_post ren env c in
	  let c = tsubst_in_predicate [result, t] c.a_value in
	  [ CC_hole c ]
    in
    CC_tuple (
      (List.map (fun id -> let id' = current_var ren id in CC_var id') ids) @
      (CC_expr t) :: hole)
    

(*s [compose k1 e1 e2 ren env] constructs the term
   
        [ let h1 = ?:P1 in ... let hn = ?:Pm in ]
          let y1,y2,...,yn, res1 [,q] = <e1 ren> in
          <e2 res1 ren'>

    where [ren' = next w1 ren] and [y1,...,yn = w1/ren] *)

let binding_of_alist ren env =
  List.map
    (fun (id,id') -> (id', CC_var_binder (trad_type_in_env ren env id)))

let insert_pre env p t ren =
  let p = apply_pre ren env p in
  let h = p.p_value in
  CC_letin (false, [pre_name p.p_name, CC_pred_binder h], CC_hole h, t ren)

let insert_many_pre env pl t =
  List.fold_left (fun t h -> insert_pre env h t) t pl

let compose info1 e1 e2 ren =
  let env = info1.env in
  let k1 = info1.kappa in
  let (res1,v1),ef1,p1,q1 = decomp_kappa k1 in
  insert_many_pre env p1
    (fun ren ->
       let w1 = get_writes ef1 in
       let ren' = next ren w1 in
       let res1,ren' = fresh ren' res1 in
       let tt1 = trad_ml_type_v ren env v1 in
       let b = [res1, CC_var_binder tt1] in
       let b',dep = match q1 with
	 | None -> 
	     [], false
	 | Some q1 -> 
	     let q1 = apply_post ren' env q1 in
	     let hyp = subst_in_predicate [Ident.result, res1] q1.a_value in
	     [post_name q1.a_name, CC_pred_binder hyp], true 
       in
       let vo = current_vars ren' w1 in
       let bl = (binding_of_alist ren env vo) @ b @ b' in
       CC_letin (dep, bl, e1 ren, e2 res1 ren'))
    (push_date ren info1.label)

(*s [cross_label] is an operator to be used when a label is encountered *)

let cross_label l e ren = e (push_date ren l)


(*s [abstraction env k e] abstracts a term [e] with respect to the 
    list of read variables, to the preconditions/assertions, i.e.
    builds

      [x1]...[xk][h1:P1]...[hn:Pn]let h'1 = ?:P'1 in ... let H'm = ?:P'm in t
    *)

let make_abs bl t = match bl with
  | [] -> t
  | _  -> CC_lam (bl, t)

let bind_pre ren env p =
  pre_name p.p_name, CC_pred_binder (apply_pre ren env p).p_value

let abs_pre env pl =
  List.fold_right
    (fun p t ->
       if p.p_assert then
	 insert_pre env p t
       else
	 (fun ren -> CC_lam ([bind_pre ren env p], t ren)))
    pl

let abstraction env k e ren =
  let _,ef,p,_ = decomp_kappa k in
  let ids = get_reads ef in
  let al = current_vars ren ids in
  let c = abs_pre env p e ren in
  let bl = binding_of_alist ren env al in
  make_abs (List.rev bl) c


(*i****

(* [make_app env ren args ren' (tf,cf) (cb,s,capp) c]
 * constructs the application of [tf] to [args].
 * capp is the effect of application, after substitution (s) and cb before
 *)

let eq ty e1 e2 =
  Papp (Ident.t_eq, [e1; e2])

let lt r e1 e2 = match r with
  | Tvar id -> Papp (id, [e1; e2])
  | _ -> assert false

let is_recursive env = function
  | CC_var x -> 
      (try let _ = find_recursion x env in true with Not_found -> false)
  | _ -> false

let if_recursion env f = function
  | CC_var x ->
      (try let v = find_recursion x env in (f v x) with Not_found -> [])
  | _ -> []

let dec_phi ren env s svi =
  if_recursion env
    (fun (phi0,(cphi,r,_)) f -> 
       let phi = subst_in_term svi (subst_in_term s cphi) in
       let phi = apply_term ren env phi in
       [CC_expr phi; CC_hole (lt r phi (Tvar phi0))])

let eq_phi ren env s svi =
  if_recursion env
    (fun (phi0,(cphi,_,a)) f ->
       let phi = subst_in_term svi (subst_in_term s cphi) in
       let phi = apply_term ren env phi in
       [CC_hole (eq a phi phi)])

let is_ref_binder = function 
  | (_,BindType (Ref _ | Array _)) -> true
  | _ -> false

let make_app env ren args ren' (tf,cf) ((bl,cb),s,capp) c =
  let ((_,tvf),ef,pf,qf) = decomp_kappa cf in
  let (_,eapp,papp,qapp) = decomp_kappa capp in
  let ((_,v),e,p,q) = decomp_kappa c in
  let bl = List.filter (fun b -> not (is_ref_binder b)) bl in
  let recur = is_recursive env tf in
  let before = current_date ren in
  let ren'' = next ren' (get_writes ef) in
  let ren''' = next ren'' (get_writes eapp) in
  let res = Ident.result in
  let vi,svi =
    let ids = List.map fst bl in
    let av = List.fold_right Idset.add ids Idset.empty in
    let s = fresh (avoid ren av) ids in
    List.map snd s, s
  in
  let tyres = v in
              (*i subst_in_constr svi (trad_ml_type_v ren env v) in i*)
  let t,ty = result_tuple ren''' before env (res, CC_var res, CC_type) (e,q) in
  let res_f = Ident.create "vf" in
  let inf,outf =
    let i,o = let _,e,_,_ = decomp_kappa cb in get_reads e, get_writes e in
    let apply_s = List.map (fun id -> try List.assoc id s with _ -> id) in
    apply_s i, apply_s o
  in
  let fe =
    let xi = List.rev (List.map snd (current_vars ren'' inf)) in
    let holes = List.map (fun x -> (apply_pre ren'' env x).p_value)
		  (List.map (pre_app (subst_in_predicate svi)) papp) in
    CC_app ((if recur then tf else CC_var res_f),
	    (dec_phi ren'' env s svi tf) 
	    @(List.map (fun id -> CC_var id) (vi @ xi))
	    @(eq_phi ren'' env s svi tf)
	    @(List.map (fun c -> CC_hole c) holes))
  in
  let qapp' = option_app (named_app (subst_in_predicate svi)) qapp in
  let t = 
    make_let_in ren'' ren''' env fe [] (current_vars ren''' outf,qapp')
      (res,tyres) (t,ty)
  in
  let t =
    if recur then 
      t
    else
      make_let_in ren' ren'' env tf pf
	(current_vars ren'' (get_writes ef),qf)
	(res_f,tvf (*i trad_ml_type_v ren env tvf i*)) (t,ty)
  in
  let rec eval_args ren = function
    | [] -> t
    | (vx,(ta,ca)) :: args ->
	let ((_,tva),ea,pa,qa) = decomp_kappa ca in
	let w = get_writes ea in
	let ren' = next ren w in
	let t' = eval_args ren' args in
	make_let_in ren ren' env ta pa (current_vars ren' (get_writes ea),qa)
	  (vx,tva (*i trad_ml_type_v ren env tva i*)) (t',ty)
  in
  eval_args ren (List.combine vi args)


(* [make_if ren env (tb,cb) ren' (t1,c1) (t2,c2)]
 * constructs the term corresponding to a if expression, i.e
 *
 *       [p] let o1, b [,q1] = m1 [?::p1] in
 *           Cases b of
 *              R => let o2, v2 [,q2] = t1  [?::p2] in 
 *                   (proj (o1,o2)), v2 [,?::q] 
 *            | S => let o2, v2 [,q2] = t2  [?::p2] in 
 *                   (proj (o1,o2)), v2 [,?::q] 
 *)

let make_if_case ren env ty (tb,qb) (br1,br2) =
  let ty1,ty2 = match qb with
    | Some q ->  
  	let q = apply_post ren env (current_date ren) q in
        (*i let q = post_app (subst_in_predicate [Ident.result,idb]) q in i*)
	decomp_boolean (Some q)
    | None ->
	print_cc_term err_formatter tb; pp_print_flush err_formatter ();
	assert false
  in
  let n = test_name Anonymous in
  (CC_if (tb, CC_lam ([n, CC_pred_binder ty1], br1),
	  CC_lam ([n, CC_pred_binder ty2], br2)))

let make_if ren env (tb,cb) ren' (t1,c1) (t2,c2) c =
  let ((_,tvb),eb,pb,qb) = decomp_kappa cb in
  let ((_,tv1),e1,p1,q1) = decomp_kappa c1 in
  let ((_,tv2),e2,p2,q2) = decomp_kappa c2 in
  let ((_,t),e,p,q) = decomp_kappa c in

  let wb = get_writes eb in
  let resb = Ident.create "resultb" in
  let res = Ident.result in
  let tyb = tvb (*i trad_ml_type_v ren' env tvb i*) in
  let tt = t (*i trad_ml_type_v ren env t i*) in

  (* une branche de if *)
  let branch cbr f_br  = 
    let (tv_br,e_br,p_br,q_br) = decomp_kappa cbr in
    let w_br = get_writes e_br in
    let ren'' = next ren' w_br in
    let t,ty = result_tuple ren'' (current_date ren') env
		 (res,CC_var res,CC_type) (e,q) in
    make_let_in ren' ren'' env f_br p_br (current_vars ren'' w_br,q_br)
      (res,tt) (t,ty),
    ty
  in
  let t1,ty1 = branch c1 t1 in
  let t2,ty2 = branch c2 t2 in
  let ty = ty1 in
  let qb = force_bool_name qb in
  let t = make_if_case ren env ty (tb,qb) (t1,t2) in
  let pre = List.map (bind_pre ren env) pb in
  make_abs pre t
(*i
  let t = make_if_case ren env ty (resb,CC_var resb,qb) (t1,t2) in
  make_let_in ren ren' env tb pb (current_vars ren' wb,None) (resb,tyb) (t,ty)
i*)


(*s [make_while ren env (cphi,r,a) (tb,cb) (te,ce) c]
   constructs the term corresponding to the while, i.e.
   \begin{verbatim}
      [h:(I x)](well_founded_induction
                A R ?::(well_founded A R)
                [Phi:A] (x) Phi=phi(x)->(I x)-> \exists x'.res.(I x')/\(S x')
                [Phi_0:A][w:(Phi:A)(Phi<Phi_0)-> ...]
                  [x][eq:Phi_0=phi(x)][h:(I x)]
                     Cases (b x) of
                       (left  HH) => (x,?::(IS x))
                     | (right HH) => let x1,_,_ = (e x ?) in
                                     (w phi(x1) ? x1 ? ?)
                phi(x) x ? ?)
   \end{verbatim}
 *)

let id_phi = Ident.create "phi"
let id_phi0 = Ident.create "phi0"

let make_body_while ren env phi_of a r id_phi0 id_w (tb,cb) tbl (i,c) =
  let ((_,tvb),eb,pb,qb) = decomp_kappa cb in
  let ((res,_),ef,_,is) = decomp_kappa c in

  let ren' = next ren (get_writes ef) in
  let before = current_date ren in
  
  let ty = 
    let is = abstract_post ren' env (ef,is) in
    let _,lo = input_output ren env c in
    product ren env before lo is 
  in
  let resb = Ident.create "resultb" in
  let tyb = tvb (*i trad_ml_type_v ren' env tvb i*) in
  let wb = get_writes eb in

  (* première branche: le test est vrai => e;w *)
  let t1 = 
    make_block ren' env 
      (fun ren'' result -> match result with
	 | Some (id,_) ->
	     let v = List.rev (current_vars ren'' (get_writes ef)) in
	       CC_app (CC_var id_w,
		       [CC_expr (phi_of ren'');
			CC_hole (lt r (phi_of ren'') (Tvar id_phi0))]
		       @(List.map (fun (_,id) -> CC_var id) v)
		       @(CC_hole (eq a (phi_of ren'') (phi_of ren'')))
		       ::(match i with
			    | None -> [] 
			    | Some c -> 
				[CC_hole (apply_assert ren'' env c).a_value])),
	       ty
      	 | None -> failwith "a block should contain at least one statement")
      tbl
  in
        
  (* deuxième branche: le test est faux => on sort de la boucle *)
  let t2,_ = 
    result_tuple ren' before env
      (res, CC_expr (Tconst ConstUnit), CC_type) (ef,is)
  in

  let b_al = current_vars ren' (get_reads eb) in
  let qb = force_bool_name qb in
  let t = make_if_case ren' env ty (tb,qb) (t1,t2) in
  let t = 
    make_let_in 
      ren' ren' env tb pb (current_vars ren' wb,qb) (resb,tyb) (t,ty) 
  in
  let t = 
    let pl = List.map (pre_of_assert false) (list_of_some i) in
    abs_pre ren' env (t,ty) pl 
  in
  let t = 
    CC_lam ([var_name Anonymous,
	     CC_pred_binder (eq a (Tvar id_phi0) (phi_of ren'))],t) 
  in
  let bl = binding_of_alist ren env (current_vars ren' (get_writes ef)) in
  make_abs (List.rev bl) t


let make_while ren env (cphi,r,a) (tb,cb) tbl (i,c) =
  let (_,ef,_,is) = decomp_kappa c in
  let phi_of ren = apply_term ren env cphi in
  let wf_a_r = Papp (Ident.well_founded, [(*i a; i*) r]) in

  let before = current_date ren in
  let ren' = next ren (get_writes ef) in
  let al = current_vars ren' (get_writes ef) in
  let v = CC_type in
(*i
  let v =   
    let _,lo = input_output ren env c in
    let is = abstract_post ren' env (ef,is) in
    match i with
      | None -> product ren' env before lo is
      | Some ci -> 
	  Term.mkArrow (apply_assert ren' env ci).a_value 
	    (product ren' env before lo is) 
  in
  let v = Term.mkArrow (eq a (mkVar id_phi) (phi_of ren')) v in
  let v = 
    n_mkNamedProd v 
      (List.map (fun (id,id') -> (id',trad_type_in_env ren env id)) al) 
  in
  let tw = 
    Term.mkNamedProd id_phi a
      (Term.mkArrow (lt r (mkVar id_phi) (mkVar id_phi0)) v) 
  in
i*)
  let id_w = Ident.create "loop" in
  let vars = List.rev (current_vars ren (get_writes ef)) in
  let body =
    make_body_while ren env phi_of a r id_phi0 id_w (tb,cb) tbl (i,c) 
  in
  CC_app (CC_expr (Tapp (well_founded_induction, [])),
	  [(*i CC_expr a; i*) CC_expr r;
	   CC_hole wf_a_r;
	   (*i CC_expr (Term.mkNamedLambda id_phi a v); i*)
	   CC_lam ([id_phi0, CC_var_binder (PureType a);
		    (*i id_w, CC_typed_binder tw i*) ],
		   body);
	   CC_expr (phi_of ren)]
	  @(List.map (fun (_,id) -> CC_var id) vars)
          @(CC_hole (eq a (phi_of ren) (phi_of ren)))
	  ::(match i with
	       | None -> [] 
	       | Some c -> [CC_hole (apply_assert ren env c).a_value])) 


(* [make_letrec ren env (phi0,(cphi,r,a)) bl (te,ce) c]
 * constructs the term corresponding to the let rec i.e.
   \begin{verbatim}
   [x][h:P(x)](well_founded_induction 
                A R ?::(well_founded A R)
                [Phi:A] (bl) (x) Phi=phi(x)->(P x)-> \exists x'.res.(Q x x')
                [Phi_0:A][w:(Phi:A)(Phi<Phi_0)-> ...]
                  [bl][x][eq:Phi_0=phi(x)][h:(P x)]te
                phi(x) bl x ? ?)
  \end{verbatim}
 *)

let make_letrec ren env (id_phi0,(cphi,r,a)) idf bl (te,ce) c =
  let (_,ef,p,q) = decomp_kappa c in
  let phi_of ren = apply_term ren env cphi in
  let wf_a_r = Papp (well_founded, [(*i a; i*) r]) in

  let before = current_date ren in
  let al = current_vars ren (get_reads ef) in
  let v = CC_type in
(*i
  let v = 
    let _,lo = input_output ren env c in
    let q = abstract_post ren env (ef,q) in
    arrow ren env (product ren env (current_date ren) lo q) p 
  in
  let v = Term.mkArrow (eq a (mkVar id_phi) (phi_of ren)) v in
  let v = 
    n_mkNamedProd v 
      (List.map (fun (id,id') -> (id',trad_type_in_env ren env id)) al) 
  in
  let v = 
    n_mkNamedProd v
      (List.map (function (id,CC_typed_binder c) -> (id,c) 
		   | _ -> assert false) (List.rev bl)) 
  in
  let tw = 
    Term.mkNamedProd id_phi a
      (Term.mkArrow (lt r (mkVar id_phi) (mkVar id_phi0)) v) 
  in
i*)
  let vars = List.rev (current_vars ren (get_reads ef)) in
  let body =
    let al = current_vars ren (get_reads ef) in
    let bod = abs_pre ren env (te,v) p in
    let bod = 
      CC_lam ([var_name Anonymous,
	       CC_pred_binder (eq a (Tvar id_phi0) (phi_of ren))],
	       bod) 
    in
    let bl' = binding_of_alist ren env al in
    make_abs (bl@(List.rev bl')) bod
  in
  let t =
    CC_app (CC_expr (Tapp (well_founded_induction, [])),
	    [(*i CC_expr a; i*) CC_expr r;
	     CC_hole wf_a_r;
	     (*i CC_expr (Term.mkNamedLambda id_phi a v); i*)
	     CC_lam ([id_phi0, CC_var_binder (PureType a);
		      (*i idf, CC_typed_binder tw i*) ],
		     body);
	     CC_expr (phi_of ren)]
	    @(List.map (fun (id,_) -> CC_var id) bl)
	    @(List.map (fun (_,id) -> CC_var id) vars)
            @[CC_hole (eq a (phi_of ren) (phi_of ren))]
	   )
  in
  (* on abstrait juste par rapport aux variables de ef *)
  let al = current_vars ren (get_reads ef) in
  let bl = binding_of_alist ren env al in
  make_abs (List.rev bl) t


****i*)
