(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: encoding_mono.ml,v 1.4 2006-11-06 14:01:15 couchot Exp $ i*)

open Cc
open Logic
open Logic_decl
open Util 

let loc = Loc.dummy_position

let prefix = "c_"
let suffix = "_c"
let var = "x"
let tvar = "t"
let cpt = ref 0
let axiomA c = (c^suffix)^ "_to_" ^ c
let axiomR c = (c^suffix)^ "_to_" ^ (c^suffix)
let def c = "def_"^c

let int2U = "int2U"
let u2Int = "u2Int"
let real2U = "real2U"
let u2Real = "u2Real" 
let bool2U = "bool2U"
let u2Bool = "u2Bool"
let arities = ref []

let int = Tapp (Ident.create (prefix^"int"), [], []) 
let real = Tapp (Ident.create (prefix^"real"), [], [])
let bool = Tapp (Ident.create (prefix^"bool"), [], []) 



(* Ground instanciation of an arity (to be plunged under) *)
let instantiate_arity id inst =
  let arity = 
    try List.assoc (Ident.string id) !arities
    with e -> (print_endline ("unknown arity :"^(Ident.string id))); raise e in
  let (vs, log_type) = Env.specialize_logic_type arity in
  match log_type with 
      Function (ptl, rt) ->
	ignore (Env.Vmap.fold 
		  (fun _ v l ->
		     (match l with [] -> [] 
			| _ -> (v.type_val <- Some (List.hd l); (List.tl l))))
		  vs (List.rev inst));
	rt
    | _ -> assert false

	

(**
   @return the list containing the type of the function/predicate parameters.
   This fucntion is called when we want to reduce the encoding of the function/predicate 
   parameter according to the type of these ones.
   @param id is the function/predicate name for which we look for the parameters 
**)
let getParamTypeList id =
  let arity = 
    try List.assoc (Ident.string id) !arities
    with e -> (print_endline ("unknown arity :"^(Ident.string id))); raise e in
  let (vs, log_type) = Env.specialize_logic_type arity in
  match log_type with 
      Function (ptl, _) -> ptl
    | Predicate ptl -> ptl


(**
   The unique type for all terms.
   this function is used everywhere we use a generic sort for the term
**) 
let ut = PTexternal ([], Ident.create (prefix^"unique"))


(**
   @param pt is the type we are going to translate.
   @return either the type if this one if a built in type (like int, float)
   or the unique type define just above
**)
let utButBuiltIn  pt = match pt with 
    PTint as k -> k 
  | PTreal as k -> k
  | PTbool as k -> k
  (*| PTvar _ -> PTexternal ([], Ident.create (prefix^"type"))*)
  | _ -> PTexternal ([], Ident.create (prefix^"unique"))


(**
   @param pt is the type we are going to translate.
   @return either the type if this one if a built in type (like int, float)
   or the unique type define in the ut function. It is a shortcut since it allows 
   to create quickly a PureType. 
**)
let utButBuiltInString  pt = match pt with 
    "PTint"  -> PTint 
  | "PTreal" -> PTreal
  | "PTbool" -> PTbool
  | _ -> 
      PTexternal ([], Ident.create (prefix^"type"))

(**
   @param ptl is the list of pure type 
   @return a list with the same size as ptl and whose only contains the 
   the type unique
**)
let unify ptl = List.map (fun _ -> ut) ptl

(**
   @param ptl is the list of pure type
   @return a list with the same size as ptl and whose only contains the 
   the type unique, but for built in type that are preserved
**)
let unifyPureType ptl = 
  List.map (fun pt -> utButBuiltIn pt) ptl

(**
   @param ptl is the list of pure type, described as string  
   @return a list with the same size as ptl and whose only contains the 
   the type unique, but for built in type that are preserved
**)
let unifyString ptl = List.map (fun pt -> utButBuiltInString pt) ptl

  

(**
   @return a forall predicate without trigger 
**)
let newForallTriggerFree is_wp x t p = 
  let n = Ident.bound x in 
  let s = Misc.subst_onev x n in
  let p = Misc.subst_in_predicate s p in
  Forall (is_wp, x, n, t, [], p) 


(**
   @return a forall predicate with triggers
   aiming at helping the prover
**)
let newForall is_wp x ty tr p = 
  let n = Ident.bound x  in
  let sp = Misc.subst_onev x n in
  let pp = Misc.subst_in_predicate sp p in
  let tt = Misc.subst_in_triggers sp tr in
  Forall (is_wp, x , n, ty, tt, pp) 


(**
   Axiomatizes the theory used in this encoding.
**) 
let prelude =
  (* The unique sort for not built-in types*)
  (Dtype (loc, [], prefix^"unique"))::	
    (Dtype (loc, [], prefix^"type"))::
    (Dtype (loc, [], prefix^"Boolean"))::
    (Dlogic (loc, prefix^"sort", 
	     Env.empty_scheme (Function ([utButBuiltInString "type" ; ut], ut)))):: 
    (Dlogic (loc, prefix^"Boolean_true",
	     Env.empty_scheme (Function ([], utButBuiltIn PTbool)))):: 
    (Dlogic (loc, prefix^"Boolean_false",
	     Env.empty_scheme (Function ([], utButBuiltIn PTbool)))):: 
    (** \forall b : bool b= true \lor b = false **)
    (Daxiom (loc, axiomR "either true_or_false",
	     let b = Ident.create "b" in 
	     let boolTrue =  Tapp (Ident.create (prefix^"Boolean_true"), [], []) in
	     let boolFalse = Tapp (Ident.create (prefix^"Boolean_false"), [], []) in 
	     let eqTrue  = Papp (Ident.t_eq, [boolTrue ; Tvar b], []) in 
	     let eqFalse  = Papp (Ident.t_eq, [boolFalse ; Tvar b], []) in 
	     let eq = Por (eqTrue, eqFalse) in 	     
	     Env.empty_scheme (newForallTriggerFree false  b  PTbool eq )))::
    (** true \neq false **)
    (Daxiom (loc, axiomR "true_neq_false",
	     let boolTrue =  Tapp (Ident.create (prefix^"Boolean_true"), [], []) in
	     let boolFalse = Tapp (Ident.create (prefix^"Boolean_false"), [], []) in 
    	     let neq = Papp (Ident.t_neq,[boolTrue;boolFalse], []) in 	     
	     Env.empty_scheme neq ))::
    
    (Dlogic (loc, int2U, 
	     Env.empty_scheme (Function ([utButBuiltIn PTint], ut)))):: 
    (Dlogic (loc, u2Int, 
	     Env.empty_scheme (Function ([ut], utButBuiltIn PTint))))::
    (Dlogic (loc, real2U, 
	     Env.empty_scheme (Function ([utButBuiltIn PTreal], ut)))):: 
    (Dlogic (loc, u2Real, 
	     Env.empty_scheme (Function ([ut], utButBuiltIn PTreal)))):: 
    (Dlogic (loc, bool2U, 
	     Env.empty_scheme (Function ([utButBuiltIn PTbool], ut))))::
    (Dlogic (loc, u2Bool, 
	     Env.empty_scheme (Function ([ut], utButBuiltIn PTbool)))):: 
    (Dlogic (loc, prefix^"int",
	     Env.empty_scheme (Function ([], utButBuiltInString "type")))):: 
    (Dlogic (loc, prefix^"bool", 
	     Env.empty_scheme (Function ([], utButBuiltInString "type"))))::
    (Dlogic (loc, prefix^"real", 
	     Env.empty_scheme (Function ([], utButBuiltInString "type"))))::
    (Dlogic (loc, prefix^"unit", 
	     Env.empty_scheme (Function ([], utButBuiltInString "type"))))::
    (Dlogic (loc, prefix^"ref", 
	     Env.empty_scheme (Function ([ut], ut))))::
    (** \forall x: Int .  u2Int(sort(int, int2U(x))) = x  (a) **)
    (Daxiom (loc, axiomR "eq_"^u2Int^"_"^int2U,
 	     let x = Ident.create "x" in 
	     let int2u_x_ = Tapp (Ident.create int2U,
				  [Tvar x], []) in 
	     let sort_int_int2U_x_ = Tapp (Ident.create (prefix^"sort"),
					   [int; int2u_x_], []) in 
	     let u2Intsort_int_int2U_x_ = Tapp (Ident.create u2Int,
						  [sort_int_int2U_x_], []) in
	     let peq = Papp (Ident.t_eq,[u2Intsort_int_int2U_x_;Tvar x], []) in 
             Env.empty_scheme (newForall false  x  PTint [[TPat sort_int_int2U_x_]]peq )))::
    (** \forall x:Real .  u2Real(sort(real, real2U(x))) = x  (b) **)
    (Daxiom (loc, axiomR "eq_"^u2Real^"_"^real2U,
	     let x = Ident.create "x" in 
	     let real2u_x_ = Tapp (Ident.create real2U,
				  [Tvar x], []) in 
	     let sort_real_real2U_x_ = Tapp (Ident.create (prefix^"sort"),
					   [real; real2u_x_], []) in 
	     let u2Realsort_real_real2U_x_ = Tapp (Ident.create u2Real,
						  [sort_real_real2U_x_], []) in
	     let peq = Papp (Ident.t_eq,[u2Realsort_real_real2U_x_;Tvar x], []) in 
             Env.empty_scheme (newForall false  x  PTreal [[TPat sort_real_real2U_x_]]peq )))::
    (** \forall x:Bool .  u2Bool(sort(bool, bool2U(x))) = x  **)
    (Daxiom (loc, axiomR "eq_"^u2Bool^"_"^bool2U,
	     let x = Ident.create "x" in 
	     let bool2u_x_ = Tapp (Ident.create bool2U,
				  [Tvar x], []) in 
	     let sort_bool_bool2U_x_ = Tapp (Ident.create (prefix^"sort"),
					   [bool; bool2u_x_], []) in 
	     let u2Boolsort_bool_bool2U_x_ = Tapp (Ident.create u2Bool,
						  [sort_bool_bool2U_x_], []) in
	     let peq = Papp (Ident.t_eq,[u2Boolsort_bool_bool2U_x_;Tvar x], []) in 
             Env.empty_scheme (newForall false  x  PTbool [[TPat sort_bool_bool2U_x_]]peq )))::
    (** \forall x. U  int2U(u2Int(sort(int,x))) = sort(int,x) **)
    (Daxiom (loc, axiomR "eq_"^int2U^"_"^u2Int,
	     let x = Ident.create "x" in 
	     let sort_int_x_ = Tapp (Ident.create (prefix^"sort"),
				     [int; Tvar x], []) in
	     let u2Int_sort_int_x_ = Tapp (Ident.create u2Int,
					   [sort_int_x_], []) in 
	     let int2U_u2Int_sort_int_x_ = Tapp (Ident.create int2U,
						 [u2Int_sort_int_x_], []) in
	     let peq = Papp (Ident.t_eq,
			     [int2U_u2Int_sort_int_x_;sort_int_x_], [])
	     in
	     Env.empty_scheme (newForall false  x ut [[TPat u2Int_sort_int_x_]]peq )))::
    (** \forall x. U  real2U(u2Real(sort(real,x))) = sort(real,x) **)
    (Daxiom (loc, axiomR "eq_"^real2U^"_"^u2Real,
	     let x = Ident.create "x" in 
	     let sort_real_x_ = Tapp (Ident.create (prefix^"sort"),
				     [real; Tvar x], []) in
	     let u2Real_sort_real_x_ = Tapp (Ident.create u2Real,
					   [sort_real_x_], []) in 
	     let real2U_u2Real_sort_real_x_ = Tapp (Ident.create real2U,
						 [u2Real_sort_real_x_], []) in
	     let peq = Papp (Ident.t_eq,
			     [real2U_u2Real_sort_real_x_;sort_real_x_], [])
	     in
	     Env.empty_scheme (newForall false  x ut [[TPat u2Real_sort_real_x_]]peq )))::
    (** \forall x. U  bool2U(u2Bool(sort(bool,x))) = sort(bool,x) **)
    (Daxiom (loc, axiomR "eq_"^bool2U^"_"^u2Bool,
	     let x = Ident.create "x" in 
	     let sort_bool_x_ = Tapp (Ident.create (prefix^"sort"),
				     [bool; Tvar x], []) in
	     let u2Bool_sort_bool_x_ = Tapp (Ident.create u2Bool,
					   [sort_bool_x_], []) in 
	     let bool2U_u2Bool_sort_bool_x_ = Tapp (Ident.create bool2U,
						 [u2Bool_sort_bool_x_], []) in
	     let peq = Papp (Ident.t_eq,
			     [bool2U_u2Bool_sort_bool_x_;sort_bool_x_], [])
	     in
	     Env.empty_scheme (newForall false  x ut [[TPat bool2U_u2Bool_sort_bool_x_]]peq )))::
    (** \forall alpha : Type, \forall x, y : Int sort(alpha,x) = sort(alpha, y) 
	     \Rightarrow 
	     x = y **)
    (Daxiom (loc, axiomR "peq",
	     let alpha = Ident.create "alpha" in
	     let x = Ident.create "x" in
	     let y = Ident.create "y"  in
	     Env.empty_scheme
	       (newForallTriggerFree false  alpha (utButBuiltInString "type")
		  (newForallTriggerFree false  x ut 
		     (newForallTriggerFree false y ut 
			(Pimplies (false, 
				   (Papp (Ident.t_eq,
					 [Tapp (Ident.create (prefix^"sort"),
						 [Tvar alpha; Tvar x], []);
					   Tapp (Ident.create (prefix^"sort"),
						 [Tvar alpha; Tvar y], [])], 
					  [])),
				   (Papp (Ident.t_eq, [Tvar x; Tvar y], [])))
		     ))))))::
    []



(** internal function used in  plunge and typedPlunge.
    it recursively translates  the type given in parameter 
    if it is a built-in type, a constant corresponding to this type is generated
    if it is a type variable, a variable corresponding to this type is generated
    @pt is the type
    @fv is list of (tag,typeVar) of the problem
**)
let rec leftt pt fv=
  match pt with
      PTint -> Tapp (Ident.create (prefix^"int"), [], [])
    | PTbool -> Tapp (Ident.create (prefix^"bool"), [], [])
    | PTreal -> Tapp (Ident.create (prefix^"real"), [], [])
    | PTunit -> Tapp (Ident.create (prefix^"unit"), [], [])
    | PTvar ({type_val = None} as var) -> 
	let t = try (List.assoc var.tag fv)
	with _ ->
	  let s = string_of_int var.tag in
	  (print_endline ("unknown vartype : "^s); Ident.create "dummy") in
	Tvar t
    | PTvar {type_val = Some pt} -> leftt pt fv 
    | PTexternal (ptl, id) -> Tapp (id, List.map (fun pt -> leftt pt fv) ptl, [])


(**@return a Tapp that encapsulates a term t with sort(..., t) 
   by calling to lefft
   @param fv is the list of type variable of the problem 
   @param term is the term we want to encapsulate
   @param pt is the type of the term
**)
let plunge fv term pt =
  Tapp (Ident.create (prefix^"sort"),
	[leftt pt fv; term],
	[])
    
(**@return a Tapp that encapsulates a term t with sort(...,f(t))
   where f is a casting function from built-in type to the unique sort
   sinc the second parameter of sort is of type unique.
   @param fv is the list of type variable of the problem 
   @param term is the term we want to encapsulate
   @param pt is the type of the term
**)
let typedPlunge fv term pt =
  (** internal function that accomplish the casting task **)
  let cast pt term = 
    match pt with
	PTint -> Tapp (Ident.create int2U,  [term], [])
      | PTbool -> Tapp (Ident.create bool2U, [term], [])
      | PTreal -> Tapp (Ident.create real2U, [term], [])
      | PTunit -> Tapp (Ident.create ("unit2U"), [term], [])
      | _ -> term 
  in
  Tapp (Ident.create (prefix^"sort"),
	[leftt pt fv; cast pt term],
	[])
    



(**
   @return the type of a term given in parameter
   @param term is the term we want the type
   @param lv is the list of (var,type) of the problem 
**)
let getTermType term lv = match term with
  | Tvar id -> 
      let associatedType = 
	(try List.assoc id lv with e ->  raise e) in
      associatedType
  | Tapp (id, l, inst) -> if (Ident.is_arith id) then
      (*(Printf.printf "is_arith : %s \n" (Ident.string id);*)
      (* TODO : update this *)
       PTint
    else
      (*(Printf.printf "is_not_rith : %s \n" (Ident.string id);*)
       instantiate_arity id inst
  | Tconst (ConstInt _)  ->  PTint
  | Tconst (ConstBool _)  -> PTbool
  | Tconst (ConstUnit)  ->  PTunit
  | Tconst (ConstFloat f) ->  PTreal
  | _ -> assert false

      




(** Translate  of a term 
    @param fv is the list of type variables of the problem 
    @param lv is the list of free  variables of the term
    @param term is the term we want to encapsulate
    @param pt is the type of the term
    
**)
let rec translate_term fv lv term isArith= 
  let translate fv lv term = match term with 
    | Tvar id as t -> 
        typedPlunge fv  (Tvar id) (getTermType t lv)
    | Tapp (id, tl, inst) when Ident.is_simplify_arith id ->
	(** This function yields a numeric parameter 
	we have to cast the result into the u type **)
	(*Printf.printf "translate_term : %s \n" (Ident.string id);*)
	let outermostCast = if Ident.is_real_arith id then  real2U 
	    else int2U in
	let inner = Tapp(Ident.create outermostCast, 
			 [Tapp(id, List.map 
				 (** each parameter of this function is numeric. 
				     We cast it to respect this constraint **)
				 (fun t -> translateNumericParam  fv lv t true ) tl, [])], 
			 []) in 
	let innerCast = if ( outermostCast= real2U) then real else int in 
	Tapp(Ident.create (prefix^"sort"), [innerCast; inner],[])
    | Tapp (id, tl, inst) ->
	(*Printf.printf "transTermApp : %s \n" (Ident.string id); *)
	(** it is not a arithmetic function **)
	(** retrieves the  function signature **)
	let paramList = ref (getParamTypeList id) in
	(** translates the paramter wrt the function signature **)
	let translateParam t  = match !paramList with 
	    PTint::tl | PTreal::tl ->
	      paramList := tl ;
	      translateNumericParam fv lv t true 
	  | _ ::tl ->
	      paramList := tl;
	      translate_term fv lv t false
	  | [] -> assert false
	in
	(** envetually encapsulates the function **)
	typedPlunge fv (Tapp (id, 
			 List.map 
			   (fun t -> translateParam t) tl, 
			 []))
	  (instantiate_arity id inst)
    | Tconst (ConstInt _) as t -> typedPlunge fv  t PTint
    | Tconst (ConstBool _) as t -> typedPlunge fv t PTbool
    | Tconst (ConstUnit) as t -> typedPlunge [] t PTunit
    | Tconst (ConstFloat f) as t -> typedPlunge fv t PTreal
    | Tderef id as t -> print_endline ("id in Tderef : "^(Ident.string id)); t 
  in
  if isArith then 
    Tapp(Ident.create u2Int, [translate fv lv term],[])
  else 
    translate fv lv term

(**
   @return a term generated by a classical translation  
   composed with a reduction that  directly applies the axioms 
   (a) and (b).
   @param fv is the list of type variables of the problem 
   @param lv is the list of variables of the term
   @param t is the term we have to translate
   @param isArith the a boolean flag used in the clasical translate_term 
   function 
**)
and translateNumericParam fv lv t isArith =
  let tp = translate_term fv lv t isArith in
  match tp with 
      Tapp(id1, [ti],_) when 
	Ident.string id1 = u2Int ->
	  begin 
	    match ti with       
		Tapp(id2, [_;tk],_) when 
		  Ident.string id2 = prefix^"sort" -> 
		    begin
		      match tk with       
			  Tapp(id3, [tl],_) when 
			    Ident.string id3 = int2U -> 
			      tl
			| _ -> tp
		    end
	      | _ -> tp 
	  end
    | Tapp(id1, [ti],_) when 
	Ident.string id1 = u2Real ->
	  begin 
	    match ti with       
		Tapp(id2, [_;tk],_) when 
		  Ident.string id2 = prefix^"sort" -> 
		    begin
		      match tk with       
			  Tapp(id3, [tl],_) when 
			    Ident.string id3 = real2U -> 
			      tl
			| _ -> tp
		    end
	      | _ -> tp 
	  end
    | _ -> tp
	
(**
   @return a predicate that is universally quantified 
   with the top most variable present in the list l. 
   These varaible are of sort type. 
   When it is the last variable into the list, it adds trigger
   When the type variable list is empty, it returns only the predicate  
   It is called when we build an axiom at the outermost position
   @param l is a list of type variables 
   @param p is the predicate we want to add quantifiers 
   @param t is the triggers 
**)
let rec lifted  l p t =  
  match l with [] -> p
    | (_, s)::[] ->
	newForall false s (utButBuiltInString "type") t p
	  
    | (_, s)::q -> 
	newForallTriggerFree false s (utButBuiltInString "type") (lifted q p t)
	  
(**
   @return a predicate that is universally quantified 
   with the top most variable present in the list l.
   When it is the last variable into the list, it adds trigger
   When the variable list is empty, it returns only the predicate  
   It is called when we build an axiom to quantify the free variables 
   @param l is a list of variables (a,t) where 
   a is the variable identifier and t is its type. 
   @param p is the predicate we want to add quantifiers 
   @param t is the triggers 
**)
let rec lifted_t l p tr =
  match l with [] -> p
    | (a,t)::[] -> 
	newForall false a t tr p    
    | (a,t)::q -> 
	newForallTriggerFree false  a t  (lifted_t q p tr)

let lifted_ctxt l cel =
  (List.map (fun (pt,s) -> Svar(s, ut)) l)@cel


(** 
    @return true if all the element of tl are of sort Int or Real
    (and not sort (int,...) that is of sort u)
    @param tl is the list of terms we analyse
    @param lv is the list of free varaiables in the terms list
**)
let rec isNumericalEquality tl lv =
  (fun tl -> match tl with 
      [] -> true 
    | hd::l -> 
	begin 
	  match hd with 
	      Tapp (id, _, _) when Ident.is_simplify_arith id -> 
		isNumericalEquality l lv 
	    | Tapp (id, _, inst) ->
		begin
		  (*Printf.printf "isMumEq : %s \n" (Ident.string id);*)
		  match (instantiate_arity id inst) with 
		    PTint | PTreal -> isNumericalEquality l lv 
		  | _ ->  false 
		end
	    | Tconst (ConstInt _) 
            | Tconst (ConstFloat _) -> isNumericalEquality l lv 
	    | Tvar id -> 
		begin 
		  match (try List.assoc id lv
			 with e ->  raise e)  with 
		      PTint | PTreal -> isNumericalEquality l lv 
		    | _ ->  false 
		end
	    | _ -> false 
	end) tl  


(** 
    @param fv is the list of type variables of the problem 
    @param p is the predicate we have to translate
    @param lv is the list of free variables in the predicate 
**)
let rec translate_pred fv lv p  = match p with
  | Papp (id, tl, inst) when  
      Ident.is_simplify_arith id ->
      Papp (id, List.map (fun t-> translateNumericParam fv lv t true) tl, []) 
  | Papp (id, tl, inst) when  
      ((Ident.is_eq id || Ident.is_neq id)  &&  isNumericalEquality tl lv )->
      Papp (id, List.map (fun t-> translateNumericParam fv lv t true) tl, [])
  | Papp (id, tl, inst) when  
      (Ident.is_eq id || Ident.is_neq id)   ->
      Papp (id, List.map (fun t-> translate_term fv lv t false) tl, []) 
  | Papp (id, tl, inst) ->
      (** retrieves the predicate signature **) 
      let paramList = ref (getParamTypeList id) in
      let translateParam t  = match !paramList with 
	  PTint::tl | PTreal::tl ->
	    paramList := tl ;
	    translateNumericParam fv lv t true 
	| _ ::tl ->
	    paramList := tl;
	    translate_term fv lv t false
	  | [] -> assert false
      in	
      Papp (id, 
	    List.map 
	      (fun t -> translateParam t) tl, 
	    [])
  | Pimplies (iswp, p1, p2) ->
      Pimplies (iswp, translate_pred fv lv p1, translate_pred fv lv p2)
  | Pif (t, p1, p2) ->
      Pif (translate_term fv lv t false, translate_pred fv lv p1, translate_pred fv lv p2)
  | Pand (iswp, issym, p1, p2) ->
      Pand (iswp, issym, translate_pred fv lv p1, translate_pred fv lv p2)
  | Por (p1, p2) ->
      Por (translate_pred fv lv p1, translate_pred fv lv p2)
  | Piff (p1, p2) ->
      Piff (translate_pred fv lv p1, translate_pred fv lv p2)
  | Pnot p ->
      Pnot (translate_pred fv lv p)
  | Forall (iswp, id, n, pt, tl, p) ->
      let lv' = (n,pt)::lv in
      let tl' = List.map (List.map (translate_pattern fv lv')) tl in
      Forall (iswp, id, n, utButBuiltIn pt, tl', translate_pred fv lv' p)
  | Forallb (iswp, p1, p2) ->
      Forallb (iswp, translate_pred fv lv p1, translate_pred fv lv p2)
  | Exists (id, n, pt, p) ->
      Exists (id, n, utButBuiltIn pt, translate_pred fv ((n,pt)::lv) p)
  | Pnamed (s, p) ->
      Pnamed (s, translate_pred fv lv p)
  | _ as d -> d 

and translate_pattern fv lv = function
  | TPat t -> TPat (translate_term fv lv t false)
  | PPat p -> PPat (translate_pred fv lv p)


(* The core *)
let queue = Queue.create ()

let rec push d = 
  try (match d with
	   (* A type declaration is translated as new logical function, the arity of *)
	   (* which depends on the number of type variables in the declaration *)
	 | Dtype (loc, vars, ident) ->
	     Queue.add (Dlogic (loc, ident, 
				Env.empty_scheme (Function (unifyString vars, utButBuiltInString "type")))) queue
	       (* For arithmetic symbols, another encoding is used (see encoding_rec.ml) *)
	 | Dlogic (loc, ident, arity) when Ident.is_simplify_arith (Ident.create ident) ->
	     arities := (ident, arity)::!arities;
	     (* with type u, and its complete arity is stored for the encoding *)
	 | Dlogic (loc, ident, arity) -> 
	     arities := (ident, arity)::!arities;
	     let newarity = match arity.Env.scheme_type with
		 Predicate ptl -> Predicate (unifyPureType ptl)
	       | Function (ptl, rt) -> Function (unifyPureType ptl, utButBuiltIn rt) in
	     
	     Queue.add (Dlogic (loc, ident,
				Env.empty_scheme newarity)) queue
	       (* A predicate definition can be handled as a predicate logic definition + an axiom *)
	 | Dpredicate_def (loc, ident, pred_def_sch) ->
	     let (argl, pred) = pred_def_sch.Env.scheme_type in
	     let rootexp = (Papp (Ident.create ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
	     push (Dlogic (loc, ident, (Env.generalize_logic_type (Predicate (snd (List.split argl))))));
	     let pred_scheme = (lifted_t argl (Piff (rootexp, pred)) [[PPat rootexp]]) in
	     push (Daxiom (loc, def ident, 
			   (Env.generalize_predicate 
			      pred_scheme)))
	       (* A function definition can be handled as a function logic definition + an axiom *)
	 | Dfunction_def (loc, ident, fun_def_sch) ->
	     let _ = print_endline ident in
	     let (argl, rt, term) = fun_def_sch.Env.scheme_type in
	     let rootexp = (Tapp (Ident.create ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
	     push (Dlogic (loc, ident, (Env.generalize_logic_type (Function (snd (List.split argl), rt)))));
	     let pred_scheme = (Env.generalize_predicate
				  (lifted_t argl 
				     (Papp (Ident.t_eq, [rootexp; term], [])) 
				     [[TPat rootexp]])) in 
	     push (Daxiom (loc, def ident,pred_scheme))
	       (* Axiom definitions *)
	 | Daxiom (loc, ident, pred_sch) ->
	     let cpt = ref 0 in
	     let fv = Env.Vset.fold
	       (fun tv acc -> 
		  cpt := !cpt + 1;
		  (tv.tag, Ident.create (tvar^(string_of_int !cpt)))::acc)
	       (pred_sch.Env.scheme_vars) [] in
	     let new_pred = (translate_pred fv [] pred_sch.Env.scheme_type) in 
	     let new_axiom =
	       Env.empty_scheme (lifted fv new_pred []) in
	     Queue.add (Daxiom (loc, ident, new_axiom)) queue
	       (* A goal is a sequent : a context and a predicate and both have to be translated *)
	 | Dgoal (loc, ident, s_sch) ->
	     let cpt = ref 0 in
	     let fv = Env.Vset.fold
	       (fun tv acc -> cpt := !cpt + 1;  (tv.tag, Ident.create (tvar^(string_of_int !cpt)))::acc)
	       (s_sch.Env.scheme_vars) [] in
	     (* function for the following fold_left *)
	     let f  (acc_c, acc_new_cel) s = match s with
		 Spred (id, p) -> (acc_c, 
				   (Spred (id, translate_pred fv acc_c p))::acc_new_cel)
	       | Svar (id, t) -> ((id,t)::acc_c, (Svar (id, utButBuiltIn t))::acc_new_cel) in
	     (* list for the following fold_left *)
	     let l = fst s_sch.Env.scheme_type in
	     let (context, new_cel) =  List.fold_left 	f ([], []) l in
	     let new_sequent =
	       Env.empty_scheme
		 (lifted_ctxt fv (List.rev new_cel),
		  translate_pred fv context (snd (s_sch.Env.scheme_type))) in
	     let temp = Dgoal (loc, ident, new_sequent) in
	     Queue.add temp queue 
      )
  with
      Not_found -> 
	Format.eprintf "Exception Caught In : %a\n" Util.print_decl d;
	raise Not_found

let iter f =
  (* first the prelude *)
  List.iter f prelude;
  (* then the queue *)
  Queue.iter f queue

let reset () = 
  arities := [];
  Queue.clear queue;
  (*List.iter push arith_kernel*)
  

