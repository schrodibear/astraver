open Jc_stdlib
open Jc_env
open Jc_envset
open Jc_region
open Jc_ast
open Jc_fenv

open Jc_name
open Jc_constructors
open Jc_pervasives
open Jc_separation
open Jc_struct_tools
open Jc_effect
open Jc_interp_misc
open Jc_invariants
open Jc_pattern

open Output
open Format
open Pp

open Jc_interp

let ft_suffix = "_ft"

(******************************************************************************)
(*                               Logic functions                              *)
(******************************************************************************)

(* let tr_logic_const vi init acc = *)
(*   let decl = *)
(*     Logic (false, vi.jc_var_info_final_name, [], tr_base_type vi.jc_var_info_type) :: acc *)
(*   in *)
(*     match init with *)
(*       | None -> decl *)
(*       | Some(t,ty) -> *)
(*           let t' = term ~type_safe ~global_assertion:true ~relocate:false LabelHere LabelHere t in *)
(*           let vi_ty = vi.jc_var_info_type in *)
(*           let t_ty = t#typ in *)
(*           (\* eprintf "logic const: max type = %a@." print_type ty; *\) *)
(*           let pred = *)
(*             LPred ( *)
(*               "eq", *)
(*               [term_coerce Loc.dummy_position ty vi_ty t (LVar vi.jc_var_info_name);  *)
(*                term_coerce t#pos ty t_ty t t']) *)
(*           in *)
(*         let ax = *)
(*           Axiom( *)
(*             vi.jc_var_info_final_name ^ "_value_axiom", *)
(*             bind_pattern_lets pred *)
(*           ) *)
(*         in *)
(*         ax::decl *)

let tr_logic_fun f ta acc =

  if Jc_options.debug then
    Format.printf "[interp] logic function %s@." f.jc_logic_info_final_name;

  let lab = 
    match f.jc_logic_info_labels with [lab] -> lab | _ -> LabelHere
  in
  let fa = 
    assertion ~type_safe:false ~global_assertion:true ~relocate:false lab lab 
  in
  let ft =
    term ~type_safe:false ~global_assertion:true ~relocate:false lab lab 
  in
  let term_coerce = term_coerce ~type_safe:false ~global_assertion:true lab in
  let params =
    List.map (tparam ~label_in_name:true lab) f.jc_logic_info_parameters
  in  
  let model_params = 
    tmodel_parameters ~label_in_name:true f.jc_logic_info_effects 
  in
  let params = params @ model_params in
  let params = List.map (fun (n,_v,ty') -> (n,ty')) params in

  (* Function definition *)
  let acc =  
    match f.jc_logic_info_result_type, ta with
      | None, JCAssertion a -> (* Predicate *)
          let body = fa a in
          Predicate(false, f.jc_logic_info_final_name, params, body) :: acc
      | Some ty, JCTerm t -> (* Function *)
          let ty' = tr_base_type ty in
          let t' = ft t in
	  let t' = term_coerce t#pos ty t#typ t t' in
          Function(false, f.jc_logic_info_final_name, params, ty', t') :: acc
      | ty_opt, JCReads r -> (* Logic *)
          let ty' = match ty_opt with
	    | None -> simple_logic_type "prop"
	    | Some ty -> tr_base_type ty
          in
          Logic(false, f.jc_logic_info_final_name, params, ty') :: acc
(*
      | ty_opt, JCAxiomatic l  ->
          let ty' = match ty_opt with
	    | None -> simple_logic_type "prop"
	    | Some ty -> tr_base_type ty
          in
	  let acc =
	    List.fold_right
	      (fun (id,a) acc -> 
		 tr_axiom id#pos id#name ~is_axiom:true f.jc_logic_info_labels a acc)
	      l acc 
	  in
	  Logic(false, f.jc_logic_info_final_name, params, ty') :: acc
*)
      | None, JCInductive l  ->
	  Inductive(false, f.jc_logic_info_final_name, params,  
		    List.map 
		      (fun (id,labels,a) ->
			 let ef = Jc_effect.assertion empty_effects a in
			 let a' = fa a in
			 let params = 
			   tmodel_parameters ~label_in_name:true ef 
			 in
			 let a' = 
			   List.fold_right 
			     (fun (n,_v,ty') a' -> LForall(n,ty',[],a')) params a' 
			 in 
			 (id#name, a')) l) :: acc
      | Some _, JCInductive _ -> assert false
      | None, JCTerm _ -> assert false 
      | Some _, JCAssertion _ -> assert false 
  in

  (* no_update axioms *)
(* TODO francois: use computed effects instead *)
  let acc = 
    match ta with 
      |	JCAssertion _ | JCTerm _ | JCInductive _ -> acc 
      | JCReads [] -> acc (* TODO: diff "reads \nothing" and nothing *)
      | JCReads pset ->
    let memory_params_reads = 
      tmemory_detailed_params ~label_in_name:true f.jc_logic_info_effects
    in
    let params_names = List.map fst params in
    let normal_params = List.map (fun name -> LVar name) params_names in
    snd (List.fold_left
      (fun (count,acc) param ->
	 let paramty = snd param in
         (* Pourquoi parcourir params et tester au lieu de parcourir
            params_memory*)
	 if not (is_memory_type paramty) then count,acc else
	   let (mc,r),_ = (* Recover which memory it is exactly *)
	     List.find (fun ((mc,r),(n,_v,_ty')) -> n = fst param) 
	       memory_params_reads
	   in
	   let zonety,basety = deconstruct_memory_type_args paramty in
	   let pset = 
	     reads ~type_safe:false ~global_assertion:true pset (mc,r) 
	   in
	   let sepa = LNot(LPred("in_pset",[LVar "tmp";pset])) in
	   let update_params = 
             List.map (fun name ->
			 if name = fst param then
			   LApp("store",[LVar name;LVar "tmp";LVar "tmpval"])
			 else LVar name
		      ) params_names
	   in
	   let a = 
             match f.jc_logic_info_result_type with
	       | None ->
		   LImpl(
                     sepa,
                     LIff(
		       LPred(f.jc_logic_info_final_name,normal_params),
		       LPred(f.jc_logic_info_final_name,update_params)))
	       | Some rety ->
		   LImpl(
                     sepa,
                     LPred("eq",[
			     LApp(f.jc_logic_info_final_name,normal_params);
			     LApp(f.jc_logic_info_final_name,update_params)]))
	   in
	   let a = 
             List.fold_left (fun a (name,ty) -> LForall(name,ty,[],a)) a params
	   in
	   let a = 
             LForall(
	       "tmp",raw_pointer_type zonety,[],
	       LForall(
		 "tmpval",basety,[],
		 a))
	   in
	   let name = 
	     "no_update_" ^ f.jc_logic_info_name ^ "_" ^ string_of_int count
	   in
	   count + 1, Axiom(name,a) :: acc
      ) (0,acc) params)
  in
(**)

  (* no_assign axioms *)
(* WRONG when JCreads [], it does not distinghishes between no reads and reads \nothing
   TODO: use computed effects instead *)
  let acc = 
    match ta with 
      | JCAssertion _ | JCTerm _ | JCInductive _ -> acc 
      | JCReads [] -> acc (* TODO: diff "reads \nothing" and nothing *)
      | JCReads pset ->
    let memory_params_reads = 
      tmemory_detailed_params ~label_in_name:true f.jc_logic_info_effects
    in
    let params_names = List.map fst params in
    let normal_params = List.map (fun name -> LVar name) params_names in
    snd (List.fold_left
      (fun (count,acc) param ->
	 let paramty = snd param in
	 if not (is_memory_type paramty) then count,acc else
	   let (mc,r),_ = (* Recover which memory it is exactly *)
	     List.find (fun ((mc,r),(n,_v,_ty')) -> n = fst param) 
	       memory_params_reads
	   in
	   let zonety,basety = deconstruct_memory_type_args paramty in
	   let pset = 
	     reads ~type_safe:false ~global_assertion:true pset (mc,r) 
	   in
	   let sepa = LPred("pset_disjoint",[LVar "tmp";pset]) in
	   let upda = 
	     LPred("not_assigns",[LVar "tmpalloc"; LVar (fst param);
				  LVar "tmpmem"; LVar "tmp"])
	   in
	   let update_params = 
             List.map (fun name ->
			 if name = fst param then LVar "tmpmem"
			 else LVar name
		      ) params_names
	   in
	   let a = 
             match f.jc_logic_info_result_type with
	       | None ->
		   LImpl(
                     make_and sepa upda,
                     LIff(
		       LPred(f.jc_logic_info_final_name,normal_params),
		       LPred(f.jc_logic_info_final_name,update_params)))
	       | Some rety ->
		   LImpl(
                     make_and sepa upda,
                     LPred("eq",[
			     LApp(f.jc_logic_info_final_name,normal_params);
			     LApp(f.jc_logic_info_final_name,update_params)]))
	   in
	   let a = 
             List.fold_left (fun a (name,ty) -> LForall(name,ty,[],a)) a params
	   in
	   let a = 
             LForall(
	       "tmp",raw_pset_type zonety,[],
               LForall(
		 "tmpmem",paramty,[],
		 LForall(
		   "tmpalloc",raw_alloc_table_type zonety,[],
		 a)))
	   in
	   let name = 
	     "no_assign_" ^ f.jc_logic_info_name ^ "_" ^ string_of_int count
	   in
	   count + 1, Axiom(name,a) :: acc
      ) (0,acc) params) (* memory_param_reads ? *)
  in
(**)

  (* alloc_extend axioms *)
(* TODO: use computed effects instead
  let acc = 
    match ta with 
      | JCAssertion _ | JCTerm _ | JCInductive _ -> acc 
      | JCReads ps ->
    let alloc_params_reads = 
      talloc_table_params ~label_in_name:true f.jc_logic_info_effects
    in
    let params_names = List.map fst params in
    let normal_params = List.map (fun name -> LVar name) params_names in
    snd (List.fold_left
      (fun (count,acc) (n,_v,paramty) ->
	 assert (is_alloc_table_type paramty);
	 let exta = 
	   LPred("alloc_extends",[LVar n; LVar "tmpalloc"])
	 in
	 let ps = 
	   List.map 
	     (collect_pset_locations ~type_safe:false ~global_assertion:true) ps
	 in
	 let ps = location_list' ps in
	 let valida =
	   LPred("valid_pset",[LVar n; ps])
	 in
	 let update_params = 
           List.map (fun name ->
		       if name = n then LVar "tmpalloc"
		       else LVar name
		    ) params_names
	 in
	 let a = 
           match f.jc_logic_info_result_type with
	     | None ->
		 LImpl(
                   make_and exta valida,
                   LIff(
		     LPred(f.jc_logic_info_final_name,normal_params),
		     LPred(f.jc_logic_info_final_name,update_params)))
	     | Some rety ->
		 LImpl(
                   make_and exta valida,
                   LPred("eq",[
			   LApp(f.jc_logic_info_final_name,normal_params);
			   LApp(f.jc_logic_info_final_name,update_params)]))
	 in
	 let a = 
           List.fold_left (fun a (name,ty) -> LForall(name,ty,a)) a params
	 in
	 let a = 
	   LForall(
	     "tmpalloc",paramty,
	     a)
	 in
	 let name = 
	   "alloc_extend_" ^ f.jc_logic_info_name ^ "_" ^ string_of_int count
	 in
	 count + 1, Axiom(name,a) :: acc
      ) (0,acc) alloc_params_reads)
  in
*)

  acc

(*   (\* full_separated axioms. *\) *)
(*   let sep_preds =  *)
(*     List.fold_left (fun acc vi -> *)
(*       match vi.jc_var_info_type with *)
(*         | JCTpointer(st,_,_) ->  *)
(*             LPred("full_separated",[LVar "tmp"; LVar vi.jc_var_info_final_name]) *)
(*             :: acc *)
(*         | _ -> acc *)
(*     ) [] li.jc_logic_info_parameters *)
(*   in *)
(*   if List.length sep_preds = 0 then acc else *)
(*     let params_names = List.map fst params_reads in *)
(*     let normal_params = List.map (fun name -> LVar name) params_names in *)
(*     MemoryMap.fold (fun (mc,r) labels acc -> *)
(*       let update_params =  *)
(*         List.map (fun name -> *)
(*           if name = memory_name(mc,r) then *)
(*             LApp("store",[LVar name;LVar "tmp";LVar "tmpval"]) *)
(*           else LVar name *)
(*         ) params_names *)
(*       in *)
(*       let a =  *)
(*         match li.jc_logic_info_result_type with *)
(*           | None -> *)
(*               LImpl( *)
(*                 make_and_list sep_preds, *)
(*                 LIff( *)
(*                   LPred(li.jc_logic_info_final_name,normal_params), *)
(*                   LPred(li.jc_logic_info_final_name,update_params))) *)
(*           | Some rety -> *)
(*               LImpl( *)
(*                 make_and_list sep_preds, *)
(*                 LPred("eq",[ *)
(*                   LApp(li.jc_logic_info_final_name,normal_params); *)
(*                   LApp(li.jc_logic_info_final_name,update_params)])) *)
(*       in *)
(*       let a =  *)
(*         List.fold_left (fun a (name,ty) -> LForall(name,ty,a)) a params_reads *)
(*       in *)
(*       let structty = match mc with  *)
(*         | FVfield fi -> JCtag(fi.jc_field_info_struct, []) *)
(*         | FVvariant vi -> JCvariant vi *)
(*       in *)
(*       let basety = match mc with *)
(*         | FVfield fi -> tr_base_type fi.jc_field_info_type *)
(*         | FVvariant vi ->  *)
(*             if integral_union vi then why_integer_type else *)
(*               simple_logic_type (union_memory_type_name vi) *)
(*       in *)
(*       let a =  *)
(*         LForall( *)
(*           "tmp",pointer_type structty, *)
(*           LForall( *)
(*             "tmpval",basety, *)
(*             a)) *)
(*       in *)
(*       let mcname = match mc with *)
(*         | FVfield fi -> fi.jc_field_info_name *)
(*         | FVvariant vi -> vi.jc_root_info_name *)
(*       in *)
(*       Axiom( *)
(*         "full_separated_" ^ li.jc_logic_info_name ^ "_" ^ mcname, *)
(*         a) :: acc *)
(*     ) li.jc_logic_info_effects.jc_effect_memories acc *)

