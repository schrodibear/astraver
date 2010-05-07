(********************************************************************************)
(*                                                                              *)
(*  The Why platform for program certification                                  *)
(*                                                                              *)
(*  Copyright (C) 2002-2010                                                     *)
(*                                                                              *)
(*    Yannick MOY, Univ. Paris-sud 11                                           *)
(*    Jean-Christophe FILLIATRE, CNRS                                           *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                                 *)
(*    Romain BARDOU, Univ. Paris-sud 11                                         *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                        *)
(*                                                                              *)
(*  Secondary contributors:                                                     *)
(*                                                                              *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)                *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)              *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)              *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hypothesis pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                             *)
(*                                                                              *)
(*  This software is free software; you can redistribute it and/or              *)
(*  modify it under the terms of the GNU Lesser General Public                  *)
(*  License version 2.1, with the special exception on linking                  *)
(*  described in file LICENSE.                                                  *)
(*                                                                              *)
(*  This software is distributed in the hope that it will be useful,            *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of              *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                        *)
(*                                                                              *)
(********************************************************************************)

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

let prop_type = "prop"
let ft_suffix = "_ft"
let notin_suffix = "_notin"
let mybag_suffix = "mybag"
let tmp_suffix = "_tmp_name"

let jc_axiom = "_jc_axiom_"

let remove_double compare l = 
  match List.fast_sort compare l with
    | [] -> []
    | ele::l ->
        let rec aux ele = function
          | [] -> []
          | a::l when compare ele a = 0 -> aux ele l
          | a::l -> a::(aux a l) in
        ele::(aux ele l)

(** Petits Modules bien utiles *)
module MyBag = 
struct
  let add_suffix s = s^"_"^mybag_suffix

  let nin = add_suffix "in"
  let nrem = add_suffix "rem"
  let ninter = add_suffix "inter"

  let nempty = add_suffix "empty"
  let nall = add_suffix "all"


  let make_in elt set =
    LPred (nin,[elt;set])

  let empty = LVar nempty
  let all = LVar nall

  let make_rem elt set =
    if set == empty 
    then empty
    else LApp(nrem,[elt;set])


  let make_inter set1 set2 =
    match set1 == all, set1, set2 == all, set2 with
      | true , _ , _ , set | _ , set, true, _ -> set
      | _ ->  LApp(ninter,[set1;set2])

  let ty ty = { logic_type_name = mybag_suffix;
                        logic_type_args = [ty]
              }

  let ty_elt = function
    | {logic_type_args = [ty]} -> ty
    | _ -> assert false


  type elt_set =
      [ `Empty | `All | `MyBag of term 
      | `Elt of term]

  (* this order is important *)
  let num = function
    | `Empty -> 1
    | `All -> 2
    | `Elt _ -> 3
    | `MyBag _ -> 4

  let compare e1 e2 = 
    let c = compare (num e1) (num e2) in
    if c <> 0 then c else compare e1 e2

  let print fmt : elt_set -> unit = function
    | `Empty -> fprintf fmt "empty"
    | `All -> fprintf fmt "all"
    | `MyBag s -> fprintf fmt "mybag(%a)" Output.fprintf_term s
    | `Elt s -> fprintf fmt "elt(%a)" Output.fprintf_term s

  let make_inter_rem_list (l:elt_set list) = 
    let rec aux  = function
    | [] -> all
    | `Empty::_ -> empty
    | `All::l -> aux l
    | `MyBag s::l -> make_inter s (aux l)
    | `Elt e::l -> make_rem e (aux l) in
    let l_s = remove_double compare l in
    Jc_options.lprintf "make_inter_rem : %a" (print_list comma print) l_s;
    aux l_s
end


(*****)
let test_correct = function
  | `Logic (f,_,_params) -> 
      if List.length f.jc_logic_info_labels <> 1 then
        failwith "Separation predicate generation :
 Logic must have only one label"
      else
        MemoryMap.iter
          (fun (mc,_distr) _labs -> 
             match mc with 
               | JCmem_field _ -> ()
               | _ -> failwith "Separation predicate generation :
 Only simple memory model"         
          )
          f.jc_logic_info_effects.jc_effect_memories
  | `Pointer _g -> ()

let if_in_restr restr e = 
  match restr with [] -> true | _ ->
    match e with
      | JCmem_field field -> List.mem field.jc_field_info_name restr
      | _ ->  assert false (* checked by test_correct *)

let inter_memory (m1,restr1) (m2,restr2) = 
  let m1 = m1.jc_logic_info_effects.jc_effect_memories in
  let m2 = m2.jc_logic_info_effects.jc_effect_memories in
  (*let log int m restr =
  Jc_options.lprintf "@[inter_memory %i:@[@.m : %a@.restr : %a@]@]"
    int
    (print_list semi (print_pair Jc_output_misc.memory_class nothing))
       (MemoryMap.keys m)
    (print_list semi string) restr;assert false in
  log 1 m1 restr1;
  log 2 m2 restr2;*)
  let filter m restr = 
    MemoryMap.filter (fun (e,_) _ -> if_in_restr restr e) m in
  let m1 = filter m1 restr1 in
  let m2 = filter m2 restr2 in
  MemoryMap.inter_merge_option 
    (fun lab1 lab2 ->
       (* These sets should have only one element has their 
          functions have only one label (see test_correct) *)
       let l1 = LogicLabelSet.choose lab1 in
       let l2 = LogicLabelSet.choose lab2 in
       Some (l1,l2)
    )
    m1 m2
(*  MemoryMap.fold
    (fun a _ acc ->
       if MemoryMap.mem a m2 
       then MemorySet.add a acc
       else acc) 
    m1 MemorySet.empty*)

let is_same_field (mc,region) var =
  let b1 = InternalRegion.equal region var.jc_var_info_region in
  let b2 = match mc with
    | JCmem_field field -> 
        Jc_typing.comparable_types field.jc_field_info_type
          var.jc_var_info_type
    | _ -> false in
  b1 && b2
  
let is_same_field_2var var1 var2 =
  InternalRegion.equal var1.jc_var_info_region var2.jc_var_info_region
  && var1.jc_var_info_type = var2.jc_var_info_type

let separation_between queue kind acc a b =
  match a,b with
    | `Logic (finfo,frestr,fparams), `Logic (ginfo,grestr,gparams) -> 
        let f = (finfo,fparams) and g = (ginfo,gparams) in
        let mems = inter_memory (finfo,frestr) (ginfo,grestr) in
        MemoryMap.fold
          (fun mem (labf,labg) acc ->
             let inc acc = Queue.add (finfo,`Notin (mem,labf)) queue;
               Queue.add (ginfo,`Ft (mem,labg)) queue;
               (`Notin_ft (g,f,mem))::acc in
             let cni acc = Queue.add (ginfo,`Notin (mem,labg)) queue;
               Queue.add (finfo,`Ft (mem,labf)) queue;
               (`Notin_ft (f,g,mem))::acc in
             match kind with
               | `Sep -> cni (inc acc)
               | `Inc -> inc acc
               | `Cni -> cni acc
          )
          mems acc
    | (`Logic (finfo,frestr,fparams), `Pointer pa) 
    | (`Pointer pa, `Logic (finfo,frestr,fparams)) ->
        let f = (finfo,fparams) in
        MemoryMap.fold
          (fun mem lab acc ->
             let lab = LogicLabelSet.choose lab in
             if is_same_field mem pa && if_in_restr frestr (fst mem)
             then 
               let incl acc = Queue.add (finfo,`Notin (mem,lab)) queue;
                 (`Notin(pa,f,mem))::acc in
               let incp acc = Queue.add (finfo,`Ft_pt (mem,lab)) queue;
                 (`Ft_pt (f,pa,mem))::acc in
               match kind, a with
                 | `Sep, _ -> incl (incp acc)
                 | `Inc, `Logic _ -> incl acc
                 | `Inc, `Pointer _ -> incp acc
                 | `Cni, `Logic _ -> incp acc
                 | `Cni, `Pointer _ -> incl acc
             else acc)
          finfo.jc_logic_info_effects.jc_effect_memories acc
    | `Pointer a, `Pointer b ->
        if is_same_field_2var a b 
        then`Diff (a,b)::acc
        else acc

let rec fold_exp f acc l = 
  let f = fun a acc b -> f acc a b in
  let rec aux acc = function
    | [] -> acc
    | a::l -> aux (List.fold_left (f a) acc l) l in
  aux acc l

let make_args ?parameters f = 
  (* From tr_logic_fun_aux *)
  let lab = 
    match f.jc_logic_info_labels with [lab] -> lab | _ -> LabelHere
  in
  let params =
    match parameters with
      | None -> f.jc_logic_info_parameters 
      | Some params -> params in 
  let params = List.map (tparam ~label_in_name:true lab) params in  
  let model_params = 
    tmodel_parameters ~label_in_name:true f.jc_logic_info_effects 
  in
  let params = params @ model_params in
  let params = List.map (fun (n,_v,ty') -> (n,ty')) params in
  params

let ft_name mem f = 
  let mem_name = memory_name mem in
  f.jc_logic_info_final_name^mem_name^ft_suffix

let ftpt_name mem f = 
  let mem_name = (memory_name mem)^"_elt" in  
  f.jc_logic_info_final_name^mem_name^ft_suffix

let notin_name mem f = 
  let mem_name = memory_name mem in  
  f.jc_logic_info_final_name^mem_name^notin_suffix

let user_predicate_code queue id kind pred =
  let (logic,_) = Hashtbl.find Jc_typing.logic_functions_table id in
  Jc_options.lprintf "Generate code of %s with %i params@." 
    logic.jc_logic_info_name (List.length pred);
  let code = fold_exp (separation_between queue kind) [] pred in
  let lab = match logic.jc_logic_info_labels with 
      [lab] -> lab | _ -> LabelHere in
  let trad_code = function
    | `Diff (a,b) -> 
        let ta = tvar ~label_in_name:true lab a in
        let tb = tvar ~label_in_name:true lab b in
        LNot (make_eq ta tb)
    | `Notin (a,(f,fparams),mem) -> 
        let params = List.map (fun (s,_) -> LVar s) 
          (make_args ~parameters:fparams f) in
        let ta = tvar ~label_in_name:true lab a in
        MyBag.make_in ta (LApp(notin_name mem f,params))
    | `Ft_pt ((f,fparams),a,mem) -> 
        let params = List.map (fun (s,_) -> LVar s) 
          (make_args ~parameters:fparams f) in
        let ta = tvar ~label_in_name:true lab a in
        let params = ta::params in
        LPred(ftpt_name mem f,params)
    | `Notin_ft ((f,fparams),(g,gparams),mem) -> 
        let g_params = List.map (fun (s,_) -> LVar s) 
          (make_args ~parameters:gparams g) in
        let tg = LApp(notin_name mem g,g_params) in
        let f_params = List.map (fun (s,_) -> LVar s)
          (make_args ~parameters:fparams f) in
        let f_params = tg::f_params in
        LPred(ft_name mem f,f_params) in
  let code = List.map trad_code code in
  let code = make_and_list code in
  let args = make_args logic in
  Predicate(false,
            logic.jc_logic_info_name,
            args,
            code)

let pragma_gen_sep = Jc_typing.pragma_gen_sep

let predicates_to_generate = Hashtbl.create 10

let compute_needed_predicates () = 
  let queue = Queue.create () in
  Hashtbl.iter (fun key value ->
                  match value with
                    | (kind,params,None) -> 
                        let code = user_predicate_code queue key kind params in
                        Hashtbl.replace pragma_gen_sep key 
                          (kind,params,Some code)
                    | (_,_,Some _) -> assert false)
    pragma_gen_sep;
  (* use the call graph to add the others needed definitions*)
  while not (Queue.is_empty queue) do
    let (f,e) = Queue.pop queue in
    let tag = f.jc_logic_info_tag in
    let l = Hashtbl.find_all predicates_to_generate tag in
    if not (List.mem e l) 
    then 
      begin 
        match e with
          | `Ft (mem,_) |`Ft_pt (mem,_) | `Notin (mem,_) ->
              if MemoryMap.mem mem 
                f.jc_logic_info_effects.jc_effect_memories then
              begin
                Hashtbl.add predicates_to_generate tag e;
                List.iter (fun called -> Queue.add (called,e) queue)
                  f.jc_logic_info_calls
              end
      end;
  done
                        
(*****)


(*****************************************************************************)
(*                              Logic functions                              *)
(*****************************************************************************)

(* let tr_logic_const vi init acc = *)
(*   let decl = *)
(*     Logic (false, vi.jc_var_info_final_name, [], 
       tr_base_type vi.jc_var_info_type) :: acc *)
(*   in *)
(*     match init with *)
(*       | None -> decl *)
(*       | Some(t,ty) -> *)
(*           let t' = term ~type_safe ~global_assertion:true ~relocate:false
             LabelHere LabelHere t in *)
(*           let vi_ty = vi.jc_var_info_type in *)
(*           let t_ty = t#typ in *)
(*           (\* eprintf "logic const: max type = %a@." print_type ty; *\) *)
(*           let pred = *)
(*             LPred ( *)
(*               "eq", *)
(*               [term_coerce Loc.dummy_position ty vi_ty t 
                 (LVar vi.jc_var_info_name);  *)
(*                term_coerce t#pos ty t_ty t t']) *)
(*           in *)
(*         let ax = *)
(*           Axiom( *)
(*             vi.jc_var_info_final_name ^ "_value_axiom", *)
(*             bind_pattern_lets pred *)
(*           ) *)
(*         in *)
(*         ax::decl *)

let fun_def f ta fa ft term_coerce params = 
  (* Function definition *)
    match f.jc_logic_info_result_type, ta with
      | None, JCAssertion a -> (* Predicate *)
          let body = fa a in
          [Predicate(false, f.jc_logic_info_final_name, params, body)]
      | Some ty, JCTerm t -> (* Function *)
          let ty' = tr_base_type ty in
          let t' = ft t in
	  let t' = term_coerce t#pos ty t#typ t t' in
          if List.mem f f.jc_logic_info_calls then
            let logic = Logic(false,f.jc_logic_info_final_name, params, ty') 
            in 
            let fstparams = List.map (fun (s,_) -> LVar s) params in
            let axiom =
              Axiom(jc_axiom^f.jc_logic_info_final_name,
                    make_forall_list params []
                      (make_eq 
                         (LApp(f.jc_logic_info_final_name,fstparams))
                         t')) in
            [logic;axiom]
          else
            [Function(false, f.jc_logic_info_final_name, params, ty', t')]
      | ty_opt, (JCNone | JCReads _) -> (* Logic *)
          let ty' = match ty_opt with
	    | None -> simple_logic_type prop_type
	    | Some ty -> tr_base_type ty
          in
          [Logic(false, f.jc_logic_info_final_name, params, ty')]
      | None, JCInductive l  ->
	  [Inductive(false, f.jc_logic_info_final_name, params,  
		    List.map 
		      (fun (id,_labels,a) ->
			 let ef = Jc_effect.assertion empty_effects a in
			 let a' = fa a in
			 let params = 
			   tmodel_parameters ~label_in_name:true ef 
			 in
			 let a' = 
			   List.fold_right 
			     (fun (n,_v,ty') a' -> LForall(n,ty',[],a')) 
                             params a' 
			 in 
			 (get_unique_name id#name, a')) l)]
      | Some _, JCInductive _ -> assert false
      | None, JCTerm _ -> assert false 
      | Some _, JCAssertion _ -> assert false

let gen_no_update_axioms f ta _fa _ft _term_coerce params acc =
    match ta with 
      |	JCAssertion _ | JCTerm _ | JCInductive _ -> acc 
      | JCNone -> acc 
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
	     List.find (fun ((_mc,_r),(n,_v,_ty')) -> n = fst param) 
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
	       | Some _rety ->
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

let gen_no_assign_axioms f ta _fa _ft _term_coerce params acc =
(* TODO: when JCNone, use computed effects instead *)
    match ta with 
      | JCAssertion _ | JCTerm _ | JCInductive _ -> acc 
      | JCNone -> acc 
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
	     List.find (fun ((_mc,_r),(n,_v,_ty')) -> n = fst param) 
	       memory_params_reads
	   in
	   let zonety,_basety = deconstruct_memory_type_args paramty in
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
	       | Some _rety ->
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

let gen_alloc_extend_axioms f ta _fa _ft _term_coerce params acc = 
(* TODO: use computed effects instead*)
    match ta with 
      | JCAssertion _ | JCTerm _ | JCInductive _ -> acc 
      | JCNone -> acc
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
	     (collect_pset_locations ~type_safe:false ~global_assertion:true) 
             ps
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
	     | Some _rety ->
		 LImpl(
                   make_and exta valida,
                   LPred("eq",[
			   LApp(f.jc_logic_info_final_name,normal_params);
			   LApp(f.jc_logic_info_final_name,update_params)]))
	 in
	 let a = 
           List.fold_left (fun a (name,ty) -> LForall(name,ty,[],a)) a params
	 in
	 let a = 
	   LForall(
	     "tmpalloc",paramty,[],
	     a)
	 in
	 let name = 
	   "alloc_extend_" ^ f.jc_logic_info_name ^ "_" ^ string_of_int count
	 in
	 count + 1, Axiom(name,a) :: acc
      ) (0,acc) alloc_params_reads)

let reduce f = function
  | [] -> assert false
  | a::l -> List.fold_left f a l

let (|>) x y = y x

let select_name = "select"

module NotIn =
struct
  type t = {
    for_one : bool; (*true if its not a bag but one element (a singleton) *)
    mem : mem_class * region;
    label : label;
    mem_name : string;
    name : string;
    ty_mem : logic_type;
  }
    

  let from_memory for_one (((mc,_distr) as m),label) = 
    let (s,_,_) = tmemory_param ~label_in_name:true label m
      (*memory_name (mc,distr)*) in
    if for_one
    then     
      {for_one = true;
       mem = m;
       label = label;
       mem_name = s;
       name = s^notin_suffix^"_elt";
       ty_mem = memory_type mc}
    else
      {for_one = false;
       mem = m;
       label = label;
       mem_name = s;
       name = s^notin_suffix;
       ty_mem = memory_type mc}

  let is_memory t m = 
    (*Jc_options.lprintf "is_memory : %s = %s@." m t.mem_name;*)
    m = t.mem_name
  let is_memory_var t = function
    | LVar m -> is_memory t m
    | _ -> false

  let notin_args t = LVar (t.name)

  let for_one t = t.for_one
  let name t = t.name
  let var t = LVar t.name
  let ty_elt t = raw_pointer_type (fst (deconstruct_memory_type_args t.ty_mem))
  let ty_elt_val t = snd (deconstruct_memory_type_args t.ty_mem)

  let ty t = 
    let ty = ty_elt t in
    if t.for_one 
    then ty 
    else MyBag.ty ty

  let mem_name t = t.mem_name
  let mem_name2 t = 
    let mem_name = memory_name t.mem in
    if t.for_one 
    then mem_name^"_elt"
    else mem_name
end

let push_not e = 
  let rec pos = function
    | LTrue| LFalse as f -> f
    | LAnd(a,b) -> LAnd(pos a,pos b)
    | LOr(a,b) -> LOr(pos a,pos b)
    | LNot a -> neg a
    | LImpl _ | LIff _ | LIf _  | LLet _ as e -> trad pos e
    | LForall (s,ty,tll,a) -> LForall(s,ty,tll,pos a)
    | LExists (s,ty,tll,a) -> LExists(s,ty,tll,pos a)
    | LPred _ as a -> a
    | LNamed (s,a) -> LNamed(s,pos a)
  and neg = function
    | LTrue -> LFalse
    | LFalse -> LTrue
    | LAnd(a,b) -> LOr(neg a,neg b)
    | LOr(a,b) -> LAnd(neg a,neg b)
    | LNot a -> pos a
    | LImpl _ | LIff _ | LIf _  | LLet _ as e -> trad neg e
    | LForall (s,ty,tll,a) -> LExists(s,ty,tll,neg a)
    | LExists (s,ty,tll,a) -> LForall(s,ty,tll,neg a)
    | LPred _ as a -> LNot a
    | LNamed (s,a) -> LNamed(s,neg a) 
  and trad f = function
    | LImpl(a,b) -> f (LOr(LNot a,b))
    | LIff(a,b) -> trad f (LAnd (LImpl(a,b),LImpl(b,a)))
    | LIf(_t,_a,_b) -> assert false (* How to trad this? t is a term *)
    | LLet _ -> assert false (* More difficult *)
    | LTrue | LFalse |LAnd _ |LOr _ | LNot _ 
    | LForall _ | LExists _ | LPred _ | LNamed _ -> assert false in
  pos e

module Def_ft_pred : 
sig  val def_ft_pred : for_one:bool -> do_rem:bool -> 'a ->
       NotIn.t -> 
       Output.why_decl list -> Output.why_decl list -> Output.why_decl list
     val ft_name : NotIn.t -> string -> string
     val ft_name_elt : NotIn.t -> string -> string
end
  =
struct
  let ft_name notin s = s^(NotIn.mem_name2 notin)^ft_suffix
  let ft_name_elt notin s = s^(NotIn.mem_name2 notin)^"_elt"^ft_suffix
      
  let add_args notin args =
    (NotIn.var notin)::args

  let add_decl_args notin args =
    (NotIn.name notin,NotIn.ty notin)::args
      
  let conv_app_pred notin s lt =
    let ft_name = ft_name notin s in
    LPred (ft_name,add_args notin lt)

  let trad_app notin e =
    match e with
      | LApp (s,[memory;elt]) when s = select_name -> 
          if NotIn.is_memory_var notin memory
          then 
            if NotIn.for_one notin
            then LNot (make_eq elt (NotIn.var notin))
            else MyBag.make_in elt (NotIn.var notin)
          else LTrue
      | LApp (s,[]) when s = select_name ->  assert false (*really impossible*)
      | LApp (s,lt) -> 
          if List.exists (NotIn.is_memory_var notin) lt
          then (conv_app_pred notin s lt)
          else LTrue
      | _ -> assert false

  let trad_pred notin e =
    match e with
      | LPred (s,lt) ->
          if List.exists (NotIn.is_memory_var notin) lt 
          then (conv_app_pred notin s lt)
          else LTrue
      | _ -> assert false

  let rec term_extract_effect notin acc e =
    match e with
      | LConst _ | LVar _ | LVarAtLabel _ -> acc
      | Tnamed (_,t) -> term_extract_effect notin acc t
      | LApp (_,lt) -> (trad_app notin e)::
          (List.fold_left (term_extract_effect notin) acc lt)
      | TIf _ -> assert false

  let rec conv_to_ft notin e = 
    match e with
      | LTrue | LFalse as f -> f
      | LAnd(a,b) -> LAnd (conv_to_ft notin a,conv_to_ft notin b)
      | LOr(a,b) -> LAnd (LImpl(a,conv_to_ft notin a),
                          LImpl(b,conv_to_ft notin b))
      | LExists (s,ty,tll,a) -> LForall (s,ty,tll,LImpl(a,conv_to_ft notin a))
      | LForall (s,ty,tll,a) -> LForall (s,ty,tll,conv_to_ft notin a)
      | LImpl _ | LIff _ | LNot _ -> assert false
      | LPred (_,lt) as e -> 
          let acc = List.fold_left 
            (term_extract_effect notin) [] lt in
          let acc = trad_pred notin e::acc in
          let acc = remove_double compare acc in
          make_and_list acc
      | LNamed (s,a) ->  LNamed(s,conv_to_ft notin a)
      | LLet _ | LIf _ -> assert false

  let generic_axiom_for_ft ~do_rem:do_rem f_name notin params acc =
    let axiom_name = "axiom"^"_"^(NotIn.mem_name notin) in
    let vars = params
        |> List.map (fun (s,_) -> LVar s) in
    let ft a = LPred (ft_name notin f_name,a::vars) in
    let ft_p a = LPred (ft_name_elt notin f_name,a::vars) in
    (* ft with rem *)
    let acc = if do_rem then
      let mb = "mb"^mybag_suffix in
      let mb_ty = NotIn.ty notin in
      let p = "p"^tmp_suffix in
      let p_ty = MyBag.ty_elt (NotIn.ty notin) in
      let assertion = LForall (mb,mb_ty,[],
                               LForall (p,p_ty,[],
                                        let mb = LVar mb in
                                        let p = LVar p in
                                        make_impl (ft mb) (make_impl (ft_p p)
                                          (ft (MyBag.make_rem p mb))))) in
      let acc = Axiom (axiom_name^"1a", 
                       make_forall_list params [] assertion)::acc in
      (* inverse *)
       let assertion = 
         let asser = 
           let mb = LVar mb in
           let p = LVar p in
           make_impl (ft (MyBag.make_rem p mb)) (ft mb) in
         LForall (mb,mb_ty,[], LForall (p,p_ty,[],asser)) in
      let acc = 
        Axiom (axiom_name^"1b", make_forall_list params [] assertion)::acc in
      let assertion = 
        let asser =
          let mb = LVar mb in
          let p = LVar p in
          make_impl (ft (MyBag.make_rem p mb)) (ft_p p) in
        LForall (mb,mb_ty,[], LForall (p,p_ty,[],asser)) in
      let acc = Axiom (axiom_name^"1c", 
                       make_forall_list params [] assertion)::acc in
      acc
    else acc in
    (* ft with inter *)
    let acc =         
      let mb1 = "mb1"^mybag_suffix in
      let mb2 = "mb2"^mybag_suffix in
      let mb_ty = NotIn.ty notin in
      let assertion = 
        let asser =
          let mb1 = LVar mb1 in
          let mb2 = LVar mb2 in
          make_equiv (make_and (ft mb1) (ft mb2))
            (ft (MyBag.make_inter mb1 mb2)) in
        LForall (mb1,mb_ty,[], LForall (mb2,mb_ty,[],asser)) in
      Axiom (axiom_name^"2", make_forall_list params [] assertion)::acc in
    (* ft with all *)
    let acc =         
      let assertion = ft MyBag.all in
      Axiom (axiom_name^"3", make_forall_list params [] assertion)::acc in
    acc

  let rec def_ft_pred ~for_one ~do_rem _f notin ta_conv acc = 
    match ta_conv with 
        (* Devrait peut-être utiliser la vrai 
           transformation d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,params,l)] -> begin 
          let name = ft_name notin f_name in
          Jc_options.lprintf "Generate logic : %s :@." name;
          let acc = Logic(false,
                          name,
                          add_decl_args notin params,
                          simple_logic_type prop_type)::acc in

          let rec gen_one_neg acc = function
            | LNot _a -> assert false (*gen_one_neg notin acc a*)
            | LPred (_id,lt) as e -> 
                (*Jc_options.lprintf "term_extract_effect %s@." id;*)
                let acc = List.fold_left 
                  (term_extract_effect notin) acc lt in
                (trad_pred notin e)::acc
            | LNamed (_,a) -> gen_one_neg acc a
            | LAnd (a,b) ->
                gen_one_neg (gen_one_neg acc b) a
            | _ -> assert false in
          let rec gen_one_pos ~impl acc = function
            | LNamed (_,a) -> gen_one_pos ~impl acc a
            | LPred (s,lt) -> (* Normalement le predicat inductif défini *)
                let asser = make_and_list acc in
                impl s lt asser
            | _ -> assert false in
          let rec gen_one ~impl acc = function
            | LForall(s,ty,tr,a) ->
                LForall(s,ty,tr,gen_one ~impl acc a)
            | LImpl (a1,a2) ->
                let acc = gen_one_neg acc a1 in
                make_impl a1 (gen_one ~impl acc a2)
            | LNamed (_,a) -> gen_one ~impl acc a
            | (LAnd _ | LOr _) -> assert false 
            | a -> gen_one_pos ~impl acc a in

          let acc = 
            if not for_one 
            then generic_axiom_for_ft ~do_rem f_name notin params acc 
            else acc in
          let acc = List.fold_left 
            (fun acc (ident,assertion) ->
               let axiom_name = 
                 "axiom"^"_ft_"^(NotIn.mem_name2 notin)^f_name^ident in
               Jc_options.lprintf "Generate axiom : %s :@." axiom_name;
               let impl s lt asser = 
                 make_impl (conv_app_pred notin s lt) asser in
               let asser = gen_one ~impl [] assertion in
               let asser = LForall (NotIn.name notin,
                                    NotIn.ty notin ,[],asser) in
               let asser = Axiom (axiom_name,asser) in
               asser::acc
            ) acc l in
          let conjs = List.map
            (fun (_ident,assertion) ->
               let impl _s lt asser = 
                 let eqs = List.map2 
                   (fun (x,_) y -> make_eq (LVar x) y) params lt in
                 make_impl (make_and_list eqs) asser in
               gen_one ~impl [] assertion) l in
          let conjs = make_and_list conjs in
          let asser = make_impl conjs 
            (conv_app_pred notin f_name 
               (List.map (fun (x,_) -> LVar x) params)) in
          let par = (NotIn.name notin,NotIn.ty notin)::params in
          let asser = make_forall_list par [] asser in
          let axiom_name = "axiom"^"_ft_"^(NotIn.mem_name2 notin)^f_name in
          let asser = Axiom (axiom_name,asser) in
          asser::acc
        end
      | [Predicate (bool,f_name,params,assertion)] ->
          let name = ft_name notin f_name in
          Jc_options.lprintf "Generate predicate : %s :@." name;
          let new_pred = Predicate (bool,
                                    name,
                                    add_decl_args notin params,
                                    conv_to_ft notin assertion) in
          new_pred::acc
      | [Function (_bool,f_name,params,_ltype,term)] ->
          let name = ft_name notin f_name in
          Jc_options.lprintf "Generate logic : %s :@." name;
          let acc = Logic(false,
                          name,
                          add_decl_args notin params,
                          simple_logic_type prop_type)::acc in

          let rec gen_one acc term =
              match term with
                | TIf(_if,_then,_else) ->
                    let acc = term_extract_effect notin acc _if in
                    LIf(_if,gen_one acc _then,gen_one acc _else)
                | e -> 
                    let acc = term_extract_effect notin acc e in
                    make_and_list acc in
          let axiom_name = "axiom"^"_ft_"^(NotIn.mem_name2 notin)^f_name in
          Jc_options.lprintf "Generate axiom : %s :@." axiom_name;
          let asser = gen_one [] term in
          let par = (NotIn.name notin,NotIn.ty notin)::params in
          let asser = make_forall_list par [] asser in
          let asser = Axiom (axiom_name,asser) in
          asser::acc
            (* Was a reccursive function definition *)
      | [Logic(_bool,f_name,params,_ltype);
         Axiom(_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          def_ft_pred ~for_one ~do_rem _f notin ta_conv acc
      | _ -> Jc_options.lprintf "@[<hov 3>I can't translate that :@\n%a" 
          (Pp.print_list Pp.newline fprintf_why_decl) ta_conv;acc
end

module Def_notin :
sig  val def_notin : 'a ->  NotIn.t -> 
       Output.why_decl list -> Output.why_decl list -> Output.why_decl list
     val def_frame_ft : string -> NotIn.t -> NotIn.t -> 
       (string * Output.logic_type) list -> Output.why_decl
     val def_frame_ft_elt: string -> NotIn.t -> NotIn.t -> 
       (string * Output.logic_type) list -> Output.why_decl
     val def_frame_notin : string -> NotIn.t -> NotIn.t -> 
       (string * Output.logic_type) list -> Output.why_decl
end
  =
struct
  let notin_name notin s = s^(NotIn.mem_name2 notin)^notin_suffix
    
  let conv_app_pred notin s lt =
    let notin_name = notin_name notin s in
    LApp (notin_name,lt)

  let trad_app notin e =
    match e with
      | LApp (s,[memory;elt]) when s = select_name -> 
          if NotIn.is_memory_var notin memory
          then `Elt elt
          else `All
      | LApp (s,_) when s = select_name ->  assert false (*really impossible*)
      | LApp (s,lt) -> 
          if List.exists (NotIn.is_memory_var notin) lt
          then (`MyBag (conv_app_pred notin s lt))
          else `All
      | _ -> assert false

  let trad_pred notin e =
    match e with
      | LPred (s,lt) ->
          if List.exists (NotIn.is_memory_var notin) lt 
          then (`MyBag (conv_app_pred notin s lt))
          else `All
      | _ -> assert false

  let rec term_extract_effect notin acc e =
    match e with
      | LConst _ | LVar _ | LVarAtLabel _ -> acc
      | Tnamed (_,t) -> term_extract_effect notin acc t
      | LApp (_,lt) -> (trad_app notin e)::
          (List.fold_left (term_extract_effect notin) acc lt)
      | TIf _ -> assert false

  let gen f_name framed_name framed_prop notin_update params framed_params = 
    let elt = "elt"^tmp_suffix in
    let elt_val = "elt_val"^tmp_suffix in
    let framed_params = framed_params@params in
    let framed_normal_params = framed_params
      |> List.map fst in
    let framed_update_params = 
      List.map (fun name ->
		  if name = NotIn.mem_name notin_update then
		    LApp("store",[LVar name;LVar elt;LVar elt_val])
		  else LVar name
	       ) framed_normal_params in
    let framed_normal_params = framed_normal_params
      |> List.map make_var in
    let params = params
      |> List.map fst 
      |> List.map make_var in
    let sepa = 
      MyBag.make_in (LVar elt) 
        (LApp (notin_name notin_update f_name,params)) in
    let a =  if framed_prop then
      LImpl(
	LPred(framed_name,framed_normal_params),
	LPred(framed_name,framed_update_params))
    else
      make_eq (LApp(framed_name,framed_normal_params))
	(LApp(framed_name,framed_update_params)) in
    let a = LImpl(sepa,a) in
    let a = make_forall_list framed_params [] a in
    let a = LForall (elt,NotIn.ty_elt notin_update,[],
                     LForall (elt_val,NotIn.ty_elt_val notin_update,[],a)) in
    let axiom_name = "axiom"^"_no_update_"^framed_name^
      (NotIn.mem_name notin_update) in
    Axiom(axiom_name,a)

  (*let def_no_update f_name notin_update params prop =
    gen f_name f_name prop notin_update params []*)

  let def_frame_ft f_name notin_update notin params =
    let ft_name = Def_ft_pred.ft_name notin f_name in
    let p = (NotIn.name notin,NotIn.ty notin) in
    gen f_name ft_name true notin_update params [p]

  let def_frame_ft_elt f_name notin_update notin params =
    let ft_name = Def_ft_pred.ft_name_elt notin f_name in
    let p = ("p"^tmp_suffix,NotIn.ty_elt notin) in
    gen f_name ft_name true notin_update params [p]

  let def_frame_notin f_name notin_update notin params =
    let notin_name = notin_name notin f_name in
    gen f_name notin_name false notin_update params []

  let rec def_notin _f notin ta_conv acc = 
    match ta_conv with 
        (* Devrait peut-être utiliser la vrai transformation 
           d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,params,l)] -> begin 

          let rec gen_one_neg notin acc = function
            | LNot _a -> assert false (*gen_one_neg notin acc a*)
            | LPred (_,lt) as e -> 
                let acc = List.fold_left 
                  (term_extract_effect notin) acc lt in
                (trad_pred notin e)::acc
            | LNamed (_,a) -> gen_one_neg notin acc a
            | LAnd (a,b) ->
                gen_one_neg notin (gen_one_neg notin acc b) a
            | _ -> assert false in
          let rec gen_one_pos notin acc = function
            | LNamed (_,a) -> gen_one_pos notin acc a
            | LPred (s,lt) -> (* Normalement le predicat inductif défini *)
                let asser = MyBag.make_inter_rem_list acc in
                make_eq (conv_app_pred notin s lt) asser
            | _ -> assert false in
          let rec gen_one notin acc = function
            | LForall(s,ty,tr,a) ->
                LForall(s,ty,tr,gen_one notin acc a)
            | LImpl (a1,a2) ->
                let acc = gen_one_neg notin acc a1 in
                make_impl a1 (gen_one notin acc a2)
            | LNamed (_,a) -> gen_one notin acc a
            | (LAnd _ | LOr _) -> assert false 
            | a -> gen_one_pos notin acc a in
          
          let name = notin_name notin f_name in
          Jc_options.lprintf "Generate logic : %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in
          List.fold_left 
            (fun acc (ident,assertion) ->
               let asser = gen_one notin [] assertion in
               let axiom_name = 
                 "axiom"^"_notin_"^(NotIn.mem_name notin) ^ident^f_name in
                 Jc_options.lprintf "Generate axiom : %s@." axiom_name;
               (*let asser = LForall (NotIn.name notin,
                                    NotIn.ty notin ,[],asser) in*)
               let asser = Axiom (axiom_name,asser) in
               asser::acc
            ) acc l
        end
      | [Predicate (bool,f_name,params,assertion)] ->
          let name = notin_name notin f_name in
          Jc_options.lprintf "Generate function : %s :@." name;
          let rec gen_one_neg notin acc = function
            | LNot _a -> assert false (*gen_one_neg notin acc a*)
            | LPred (_,lt) as e -> 
                let acc = List.fold_left 
                  (term_extract_effect notin) acc lt in
                (trad_pred notin e)::acc
            | LNamed (_,a) -> gen_one_neg notin acc a
            | LAnd (a,b) ->
                gen_one_neg notin (gen_one_neg notin acc b) a
            | _ -> assert false in
          let asser = gen_one_neg notin [] assertion in
          let new_pred = Function (bool,
                                   name,
                                   params,
                                   NotIn.ty notin,
                                   MyBag.make_inter_rem_list asser) in
          new_pred::acc
      | [Function (_bool,f_name,params,_ltype,term)] ->
          let name = notin_name notin f_name in
          Jc_options.lprintf "Generate logic : %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in

          let rec gen_one acc term =
              match term with
                | TIf(_if,_then,_else) ->
                    let acc = term_extract_effect notin acc _if in
                    LIf(_if,gen_one acc _then,gen_one acc _else)
                | e -> 
                    let acc = term_extract_effect notin acc e in
                    let acc = MyBag.make_inter_rem_list acc in
                    let params = List.map (fun (s,_) -> LVar s) params in
                    make_eq (conv_app_pred notin f_name params) acc in
          let axiom_name = "axiom"^"_notin_"^(NotIn.mem_name2 notin)^f_name in
          Jc_options.lprintf "Generate axiom : %s :@." axiom_name;
          let asser = gen_one [] term in
          let par = (NotIn.name notin,NotIn.ty notin)::params in
          let asser = make_forall_list par [] asser in
          let asser = Axiom (axiom_name,asser) in
          asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Axiom(_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          def_notin _f notin ta_conv acc
      | _ -> Jc_options.lprintf "@[<hov 3>I can't translate that :@\n%a" 
          (Pp.print_list Pp.newline fprintf_why_decl) ta_conv;acc
end

                 
let tr_logic_fun_aux f ta acc =

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
  let usual_params =
    List.map (tparam ~label_in_name:true lab) f.jc_logic_info_parameters
  in  
  let model_params = 
    tmodel_parameters ~label_in_name:true f.jc_logic_info_effects 
  in
  let _3to2 = List.map (fun (n,_v,ty') -> (n,ty')) in
  let usual_params = _3to2 usual_params in
  let model_params = _3to2 model_params in
  let params = usual_params @ model_params in
  (* definition of the function *)
  let fun_def = fun_def f ta fa ft term_coerce params in
  let acc = fun_def@acc in

  (* no_update axioms *)
  let acc = gen_no_update_axioms f ta fa ft term_coerce params acc in

  (* no_assign axioms *)
  let acc = gen_no_assign_axioms f ta fa ft term_coerce params acc in

  (* alloc_extend axioms *)
  (*let acc = gen_alloc_extend_axioms f ta fa ft term_coerce params acc in*)

  (* generation of ft *)
  let acc =
    if Jc_options.gen_frame_rule_with_ft 
    then 
      begin 
        let f_name = f.jc_logic_info_final_name in
        let todos = 
          Hashtbl.find_all predicates_to_generate f.jc_logic_info_tag in
        let filter_notin acc = function
          | `Notin mem -> (NotIn.from_memory false mem)::acc
          | _ -> acc in
        let notin_updates = List.fold_left filter_notin [] todos in
        let print_todo fmt = function
           | `Ft _ -> fprintf fmt "ft"
           | `Notin _ -> fprintf fmt "notin"
           | `Ft_pt _ -> fprintf fmt "ft_pt" in
        Jc_options.lprintf "%s asks to generate : %a@." 
          f_name (Pp.print_list Pp.comma print_todo) todos;
        let make_todo acc todo =
          match todo with
            | `Ft mem -> 
                let notin = NotIn.from_memory false mem in
                let do_rem = List.mem (`Ft_pt mem) todos in
                let acc = Def_ft_pred.def_ft_pred ~for_one:false
                  ~do_rem f notin fun_def acc in
                List.fold_left 
                (fun acc notin_update ->
                   (Def_notin.def_frame_ft f_name 
                      notin_update notin params)::acc)
                  acc notin_updates
            | `Notin mem -> 
                let notin = NotIn.from_memory false mem in
                let acc = 
                  Def_notin.def_notin f notin fun_def acc in
                List.fold_left (fun acc notin_update ->
                                  (Def_notin.def_frame_notin f_name 
                                     notin_update notin params)::acc)
                  acc notin_updates
            | `Ft_pt mem -> 
                let notin = NotIn.from_memory true mem in
                let acc = Def_ft_pred.def_ft_pred 
                  ~for_one:true ~do_rem:false  
                  f notin fun_def acc in
                let notin = NotIn.from_memory false mem in
                List.fold_left (fun acc notin_update ->
                                  (Def_notin.def_frame_ft_elt f_name 
                                     notin_update notin params)::acc)
                  acc notin_updates in
        List.fold_left make_todo acc todos
      end
    else acc in
   
  acc

(*   (\* full_separated axioms. *\) *)
(*   let sep_preds =  *)
(*     List.fold_left (fun acc vi -> *)
(*       match vi.jc_var_info_type with *)
(*         | JCTpointer(st,_,_) ->  *)
(*             LPred("full_separated",[LVar "tmp"; 
               LVar vi.jc_var_info_final_name]) *)
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
(*         List.fold_left (fun a (name,ty) -> LForall(name,ty,a)) 
           a params_reads *)
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


let tr_logic_fun ft ta acc = 
  (* If the logic function is a user generated predicate then
     we replaced it by the one previously computed *)
  if Jc_options.gen_frame_rule_with_ft &&
    Hashtbl.mem pragma_gen_sep ft.jc_logic_info_tag
  then match Hashtbl.find pragma_gen_sep ft.jc_logic_info_tag with
    | (_,_,None) -> assert false
    | (_,_,Some code) -> code::acc
  else tr_logic_fun_aux ft ta acc

(*
  Local Variables: 
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End: 
*)
