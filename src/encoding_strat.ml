(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



open Cc
open Logic
open Logic_decl

let loc = Loc.dummy_floc

let prefix = "c_"
let suffix = "_c"
let var = "x"
let tvar = "t"
let cpt = ref 0
let axiom c = c ^ "_to_" ^ (c^suffix)
let def c = "def_"^c

let arities = ref []

(* The unique type for all terms *)
let ut = PTexternal ([], Ident.create (prefix^"unique"))

let unify ptl = List.map (fun _ -> ut) ptl
    
let prelude =
  (Dtype (loc, Ident.create (prefix^"unique"), []))::	(* The unique sort *)
  (Dlogic (loc, Ident.create (prefix^"sort"),
	   Env.empty_scheme (Function ([ut; ut], ut)))):: (* The "sort" symbol *)
  (Dlogic (loc, Ident.create (prefix^"int"),
	   Env.empty_scheme (Function ([], ut)))):: (* One synbol for each prefedined type *)
  (Dlogic (loc, Ident.create (prefix^"bool"),
	   Env.empty_scheme (Function ([], ut))))::
  (Dlogic (loc, Ident.create (prefix^"real"),
	   Env.empty_scheme (Function ([], ut))))::
  (Dlogic (loc, Ident.create (prefix^"unit"),
	   Env.empty_scheme (Function ([], ut))))::
  (Dlogic (loc, Ident.create (prefix^"ref"),
	   Env.empty_scheme (Function ([ut], ut))))::
(*   (Dlogic (loc, "neq"^suffix, *)
(* 	   Env.empty_scheme (Predicate ([ut; ut])))):: *)
  (Daxiom (loc, axiom "eq",
	   let x = Ident.create "x"
	   and y = Ident.create "y" 
	   and int = Tapp (Ident.create (prefix^"int"), [], []) in
	   Env.empty_scheme
             (Forall (false, x, x, ut, [],
	      Forall (false, y, y, ut, [],
	      (Piff
		 (Papp (Ident.t_eq,
			[Tapp (Ident.create (prefix^"sort"),
			       [int; Tvar x], []);
			 Tapp (Ident.create (prefix^"sort"),
			       [int; Tvar y], [])], []),
		  (Papp (Ident.t_eq, [Tvar x; Tvar y], []))))
		     )))))::
  []

(* Special axioms for arithmetic *)
let arith_kernel =
  (Dlogic (loc, Ident.t_add_int,
	   Env.empty_scheme (Function ([PTint; PTint], PTint))))::
  (Dlogic (loc, Ident.t_sub_int,
	   Env.empty_scheme (Function ([PTint; PTint], PTint))))::
  (Dlogic (loc, Ident.t_mul_int,
	   Env.empty_scheme (Function ([PTint; PTint], PTint))))::
(*
  (Dlogic (loc, Ident.t_div_int,
	   Env.empty_scheme (Function ([PTint; PTint], PTint))))::
  (Dlogic (loc, Ident.t_mod_int,
	   Env.empty_scheme (Function ([PTint; PTint], PTint))))::
*)
  (Dlogic (loc, Ident.t_neg_int,
	   Env.empty_scheme (Function ([PTint], PTint))))::
  (Dlogic (loc, Ident.t_lt_int,
	   Env.empty_scheme (Predicate ([PTint; PTint]))))::
  (Dlogic (loc, Ident.t_le_int,
	   Env.empty_scheme (Predicate ([PTint; PTint]))))::
  (Dlogic (loc, Ident.t_gt_int,
	   Env.empty_scheme (Predicate ([PTint; PTint]))))::
  (Dlogic (loc, Ident.t_ge_int,
	   Env.empty_scheme (Predicate ([PTint; PTint]))))::
  []

(* Function that plunges a term under its type information.  *)
(* Uses an assoc. list of tags -> idents for type variables *)
let plunge fv term pt =
  let rec leftt pt =
    match pt with
      PTint -> Tapp (Ident.create (prefix^"int"), [], [])
    | PTbool -> Tapp (Ident.create (prefix^"bool"), [], [])
    | PTreal -> Tapp (Ident.create (prefix^"real"), [], [])
    | PTunit -> Tapp (Ident.create (prefix^"unit"), [], [])
    | PTvar ({type_val = None} as var) -> 
	let t = 
	  try 
	    List.assoc var.tag fv
	  with Not_found ->
	    let s = string_of_int var.tag in
	    (print_endline ("unknown vartype : "^s); s) 
	in
	Tvar (Ident.create t)
    | PTvar {type_val = Some pt} -> leftt pt
    | PTexternal (ptl, id) -> Tapp (id, List.map (fun pt -> leftt pt) ptl, [])
  in
  Tapp (Ident.create (prefix^"sort"),
	[leftt pt; term],
	[])

(* Function that strips the top most sort application, for terms bound
   in let-ins *)
let strip_topmost t =
  match t with
    | Tapp (symb, [_encoded_ty; encoded_t], []) 
	when symb = Ident.create (prefix^"sort") ->
	encoded_t
    | _ -> t

(* Ground instanciation of an arity (to be plunged under) *)
let instantiate_arity id inst =
  let arity = 
    try List.assoc (Ident.string id) !arities
    with e -> 
      (print_endline ("unknown arity for symbol "^(Ident.string id))); raise e in
  let (vs, log_type) = Env.specialize_logic_type arity in
  match log_type with 
    Function (_ptl, rt) ->
      ignore (Env.Vmap.fold (fun _ v l ->
	(match l with [] -> [] 
	| _ -> (v.type_val <- Some (List.hd l); (List.tl l))))
		vs (List.rev inst));
      rt
  | _ -> assert false

(* Translation of a term *)
let rec translate_term fv lv = function
  | Tvar id -> 
      plunge fv (Tvar id)
	(try List.assoc id lv
	with e -> (* (print_endline ("unknown variable :"^(pp id)); *)
(* 		   print_endline "=== in ==="; *)
(* 		   ignore (List.iter (fun (n, _) -> print_endline (pp n)) lv); *)
	  raise e)
  | Tapp (id, tl, _inst) when Ident.is_simplify_arith id ->
      Tapp(Ident.create (Ident.string id ^ suffix),
	   List.map (translate_term fv lv) tl, [])
  | Tapp (id, tl, inst) ->
      plunge fv (Tapp (id, List.map (translate_term fv lv) tl, []))
	(instantiate_arity id inst)
  | Tconst (ConstInt _) as t -> plunge [] t PTint
  | Tconst (ConstBool _) as t -> plunge [] t PTbool
  | Tconst (ConstUnit) as t -> plunge [] t PTunit
  | Tconst (ConstFloat _f) as t -> plunge [] t PTreal
  | Tderef id as t -> print_endline ("id in Tderef : "^(Ident.string id)); t
  | Tnamed(_,t) -> translate_term fv lv t

(* Generalizing a predicate scheme with foralls (can add a trigger) *)
let rec lifted  l p t =
  match l with [] -> p
  | (_, s)::[] ->
      Forall(false, Ident.create s, Ident.create s, ut, t, p)
  | (_, s)::q -> 
      Forall(false, Ident.create s, Ident.create s, ut, [], lifted q p t)
	
let rec lifted_t l p tr =
  match l with [] -> p
  | (a,t)::[] -> (Forall(false, a, a, t, tr, p))
  | (a,t)::q ->  (Forall(false, a, a, t, [], lifted_t q p tr))

let rec lifted_ctxt l cel =
  (List.map (fun (_,s) -> Svar(Ident.create s, ut)) l)@cel

(* Translation of a predicate *)
let rec translate_pred fv lv = function
  | Papp (id, tl, _inst) when Ident.is_simplify_arith id ->
      Papp (Ident.create ((Ident.string id)^suffix), 
	    List.map (translate_term fv lv) tl, [])
(*   | Papp (id, [a; b], inst) when Ident.is_neq id -> *)
(*       Papp (Ident.create ("neq"^suffix), [translate_term fv lv a; translate_term fv lv b], []) *)
  | Papp (id, tl, _inst) ->
      Papp (id, List.map (translate_term fv lv) tl, [])
  | Plet (id, n, pt, t, p) -> 
      let t' = strip_topmost (translate_term fv lv t) in
	Plet (id, n, ut, t', translate_pred fv ((n,pt)::lv) p)
  | Pimplies (iswp, p1, p2) ->
      Pimplies (iswp, translate_pred fv lv p1, translate_pred fv lv p2)
  | Pif (t, p1, p2) ->
      Pif (translate_term fv lv t, translate_pred fv lv p1, translate_pred fv lv p2)
  | Pand (iswp, issym, p1, p2) ->
      Pand (iswp, issym, translate_pred fv lv p1, translate_pred fv lv p2)
  | Por (p1, p2) ->
      Por (translate_pred fv lv p1, translate_pred fv lv p2)
  | Piff (p1, p2) ->
      Piff (translate_pred fv lv p1, translate_pred fv lv p2)
(*   | Pnot (Papp (id, [a; b], inst)) when Ident.is_eq id -> *)
(*       Papp (Ident.create ("neq"^suffix), [translate_term fv lv a; translate_term fv lv b], []) *)
  | Pnot p ->
      Pnot (translate_pred fv lv p)
  | Forall (iswp, id, n, pt, tl, p) ->
      let lv' = (n,pt)::lv in
(*       print_endline "----"; *)
(*       ignore (List.iter (fun (n, _) -> print_endline (Ident.string n)) lv'); *)
      let tl' = List.map (List.map (translate_pattern fv lv')) tl in
      Forall (iswp, id, n, ut, tl', translate_pred fv lv' p)
  | Forallb (iswp, p1, p2) ->
      Forallb (iswp, translate_pred fv lv p1, translate_pred fv lv p2)
  | Exists (id, n, pt, p) ->
      Exists (id, n, ut, translate_pred fv ((n,pt)::lv) p)
  | Pnamed (s, p) ->
      Pnamed (s, translate_pred fv lv p)
  | _ as d -> d 

and translate_pattern fv lv = function
  | TPat t -> TPat (translate_term fv lv t)
  | PPat p -> PPat (translate_pred fv lv p)

(* Identity for now (Could translate built-in equality into customized equality) *)
let rec translate_eq = (fun d -> d) (* function *)
(*   | Papp (id, tl, inst) when Ident.is_eq id -> *)
(*       Papp (Ident.create ("equal"^suffix), tl, inst) *)
(*   | Papp (id, tl, inst) when Ident.is_neq id -> *)
(*       Pnot (Papp (Ident.create ("equal"^suffix), tl, inst)) *)
(*   | Pimplies (iswp, p1, p2) -> *)
(*       Pimplies (iswp, translate_eq p1, translate_eq p2) *)
(*   | Pif (t, p1, p2) -> *)
(*       Pif (t, translate_eq p1, translate_eq p2) *)
(*   | Pand (iswp, issym, p1, p2) -> *)
(*       Pand (iswp, issym, translate_eq p1, translate_eq p2) *)
(*   | Por (p1, p2) -> *)
(*       Por (translate_eq p1, translate_eq p2) *)
(*   | Piff (p1, p2) -> *)
(*       Piff (translate_eq p1, translate_eq p2) *)
(*   | Pnot p -> *)
(*       Pnot (translate_eq p) *)
(*   | Forall (iswp, id, n, pt, p) -> *)
(*       Forall (iswp, id, n, pt, translate_eq p) *)
(*   | Forallb (iswp, p1, p2) -> *)
(*       Forallb (iswp, translate_eq p1, translate_eq p2) *)
(*   | Exists (id, n, pt, p) -> *)
(*       Exists (id, n, pt, translate_eq p) *)
(*   | Pnamed (s, p) -> *)
(*       Pnamed (s, translate_eq p) *)
(*   | _ as d -> d  *)

(* The core *)
let queue = Queue.create ()

let rec push d = 
  try (match d with
(* A type declaration is translated as new logical function, the arity of *)
(* which depends on the number of type variables in the declaration *)
  | Dtype (loc, ident, vars) ->
      Queue.add (Dlogic (loc, ident, 
			 Env.empty_scheme (Function (unify vars, ut)))) queue
  | Dalgtype _ ->
      assert false
(*
      failwith "encoding rec: algebraic types are not supported"
*)
(* For arithmetic symbols, another encoding is used (see encoding_rec.ml) *)
  | Dlogic (loc, ident, arity) when Ident.is_simplify_arith ident ->
      let cpt = ref 0 in
      let fv = Env.Vset.fold
	  (fun tv acc -> cpt := !cpt + 1; (tv.tag, tvar^(string_of_int !cpt))::acc)
	  (arity.Env.scheme_vars) [] in
      let name = Ident.string ident in
      (match arity.Env.scheme_type with 
      | Predicate ptl ->
	  let args = 
	    List.map
	      (fun t -> Ident.create (let _ = cpt := !cpt + 1 in var^(string_of_int !cpt)), t)
	      ptl in
	  let terml = 
	    Papp (Ident.create (name^suffix),
		  List.map (fun (id, t) -> plunge fv (Tvar id) t) args, [])
	  and termr =
	    Papp (ident, List.map (fun (t, _) -> Tvar t) args, []) in
	  let ax = Env.empty_scheme 
	      (lifted ((List.map (fun (id,_) -> (0, Ident.string id)) args)@fv)
		 (Piff (terml, termr)) [[PPat terml]]) in
	  (Queue.add (Dlogic (loc, Ident.create (name^suffix),
			      Env.empty_scheme (Predicate (unify ptl)))) queue;
	   Queue.add (Dlogic (loc, ident,
			      Env.empty_scheme (Predicate (unify ptl)))) queue;
	   Queue.add (Daxiom (loc, axiom name, ax)) queue)
      | Function (ptl, rt) ->
	  let args = 
	    List.map
	      (fun t -> 
		Ident.create (let _ = cpt := !cpt + 1 in var^(string_of_int !cpt)), t)
	      ptl in
	  let terml = 
	    Tapp (Ident.create (name^suffix),
		  List.map (fun (id, t) -> plunge fv (Tvar id) t) args, []) 
	  and termr =
	    plunge fv 
	      (Tapp (ident, List.map (fun (t, _) -> Tvar t) args, []))
	      rt in
	  let ax = Env.empty_scheme 
	      (lifted 
		 ((List.map (fun (id,_) -> (0,Ident.string id)) args)@fv)
		 (Papp (Ident.t_eq, [terml;termr], [])) [[TPat terml]]) in
	  (Queue.add (Dlogic (loc, Ident.create (name^suffix),
			      Env.empty_scheme (Function (unify ptl, ut)))) queue;
	   Queue.add (Dlogic (loc, ident,
			      Env.empty_scheme (Function (unify ptl, ut)))) queue;
	   Queue.add (Daxiom (loc, axiom name, ax)) queue))
(* In the case of a logic definition, we redefine the logic symbol  *)
(* with type u, and its complete arity is stored for the encoding *)
  | Dlogic (loc, ident, arity) -> 
      arities := (Ident.string ident, arity)::!arities;
      let newarity = match arity.Env.scheme_type with
	Predicate ptl -> Predicate (unify ptl)
      | Function (ptl, _) -> Function (unify ptl, ut) in
      Queue.add (Dlogic (loc, ident,
			 Env.empty_scheme newarity)) queue
(* A predicate definition can be handled as a predicate logic definition + an axiom *)
  | Dpredicate_def (_loc, _ident, _pred_def_sch) ->
      assert false
(*
      let (argl, pred) = pred_def_sch.Env.scheme_type in
      let rootexp = (Papp (ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
      let name = Ident.string ident in
      push (Dlogic (loc, ident, (Env.generalize_logic_type (Predicate (snd (List.split argl))))));
      push (Daxiom (loc, def name, (Env.generalize_predicate 
				       (lifted_t argl (Piff (rootexp, pred)) [[PPat rootexp]]))))
*)
  | Dinductive_def(_loc, _ident, _inddef) ->
      assert false
(*
      failwith "encoding strat: inductive def not yet supported"
*)
(* A function definition can be handled as a function logic definition + an axiom *)
  | Dfunction_def (_loc, _ident, _fun_def_sch) ->
      assert false
(*
(* ?????
      let _ = print_endline ident in
*)
      let (argl, rt, term) = fun_def_sch.Env.scheme_type in
      let rootexp = (Tapp (ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
      let name = Ident.string ident in
      push (Dlogic (loc, ident, (Env.generalize_logic_type (Function (snd (List.split argl), rt)))));
      push (Daxiom (loc, def name,
		    (Env.generalize_predicate
		       (lifted_t argl (Papp (Ident.t_eq, [rootexp; term], [])) [[TPat rootexp]]))))
*)
(* Axiom definitions *)
  | Daxiom (loc, name, pred_sch) ->
      let cpt = ref 0 in
      let fv = Env.Vset.fold
	  (fun tv acc -> cpt := !cpt + 1; (tv.tag, tvar^(string_of_int !cpt))::acc)
	  (pred_sch.Env.scheme_vars) [] in
      let new_axiom =
	Env.empty_scheme (lifted fv (translate_pred fv [] pred_sch.Env.scheme_type) []) in
      Queue.add (Daxiom (loc, name, new_axiom)) queue
(* A goal is a sequent : a context and a predicate and both have to be translated *)
  | Dgoal (loc, is_lemma, expl, name, s_sch) ->
      begin try
	let cpt = ref 0 in
	let fv = Env.Vset.fold
	  (fun tv acc -> cpt := !cpt + 1; (tv.tag, tvar^(string_of_int !cpt))::acc)
	  (s_sch.Env.scheme_vars) [] in
	let (context, new_cel) = 
	  List.fold_left 
	    (fun (acc_c, acc_new_cel) s -> match s with
		 Spred (id, p) -> (acc_c, 
				   (Spred (id, translate_eq (translate_pred fv acc_c p)))::acc_new_cel)
	       | Svar (id, t) -> ((id,t)::acc_c, (Svar (id, ut))::acc_new_cel))
	    ([], [])
	    (fst (s_sch.Env.scheme_type)) in
	let new_sequent =
	  Env.empty_scheme
	    (lifted_ctxt fv (List.rev new_cel),
	     translate_eq (translate_pred fv context (snd (s_sch.Env.scheme_type)))) in
	Queue.add (Dgoal (loc, is_lemma, expl, name, new_sequent)) queue
      with Not_found -> 
	Format.eprintf "Exception Not_found caught in : %a\n" Util.print_decl d;
	Queue.add (Dgoal (loc, is_lemma, expl, name, Env.empty_scheme([],Pfalse))) queue
      end)
  with
    Not_found -> 
      Format.eprintf "Exception Not_found caught in : %a\n" Util.print_decl d;
      raise Not_found

let iter f =
  (* first the prelude *)
  List.iter f prelude;
  (* then the queue *)
  Queue.iter f queue

let reset () = 
  arities := [];
  Queue.clear queue;
  List.iter push arith_kernel;
(*
  Env.iter_global_logic (fun id _ -> print_endline (Ident.string id));
  Env.iter_global_logic 
    (fun id lts -> push (Dlogic (loc, Ident.string id, lts)))
*)
