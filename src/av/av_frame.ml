(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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


open Stdlib
open Env
open Envset
open Region
open Ast
open Effect
open Fenv

open Name
open Constructors
open Common
open Separation
open Struct_tools
open Interp_misc
open Invariants
open Pattern

open Output_ast
open Output_misc
module Output = (val Options.backend)

open Format
open Why_pp

open Interp

open Frame_notin

(*****)

let test_correct_logic f =
  if List.length f.li_labels <> 1 then
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
      f.li_effects.e_memories

let test_correct = function
  | `Logic (f,_,_) -> test_correct_logic f
  | `Pointer _g -> ()

let if_in_restr restr e =
  match restr with [] -> true | _ ->
    match e with
      | JCmem_field field -> List.mem field.fi_name restr
      | _ ->  assert false (* checked by test_correct *)

let inter_memory (m1,restr1) (m2,restr2) =
  let m1 = m1.li_effects.e_memories in
  let m2 = m2.li_effects.e_memories in
  (*let log int m restr =
  Options.lprintf "@[inter_memory %i:@[@.m : %a@.restr : %a@]@]"
    int
    (print_list semi (print_pair Output_misc.memory_class nothing))
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
  let b1 = InternalRegion.equal region var.vi_region in
  let b2 = match mc with
    | JCmem_field field ->
        Typing.comparable_types field.fi_type
          var.vi_type
    | _ -> false in
  b1 && b2

let is_same_field_2var var1 var2 =
  InternalRegion.equal var1.vi_region var2.vi_region
  && var1.vi_type = var2.vi_type

let separation_between queue kind acc a b =
  match a,b with
    | `Logic (finfo,frestr,fparams), `Logic (ginfo,grestr,gparams) ->
        let f = (finfo,fparams) and g = (ginfo,gparams) in
        let mems = inter_memory (finfo,frestr) (ginfo,grestr) in
        MemoryMap.fold
          (fun mem (labf,labg) acc ->
             let memlf = NotIn.from_memory false (mem,labf) in
             let memlg = NotIn.from_memory false (mem,labg) in
             let disj acc =
               Queue.add (finfo,(`Disj ,memlf)) queue;
               Queue.add (ginfo,(`Disj ,memlg)) queue;
               (`Disj ((g,memlg),(f,memlf)))::acc in
             match kind with
               | `Sep -> disj acc
               | `Inc -> assert false (* Not Done anymore *)
               | `Cni -> assert false (* Not Done anymore *)
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
               let meml = NotIn.from_memory false (mem,lab) in
               let inn acc =
                 Queue.add (finfo,(`In, meml))  queue;
                 (`In(pa,f,meml))::acc in
               match kind, a with
                 | `Sep, _ -> inn acc
                 | `Inc, `Logic _ -> assert false (* Not Done anymore *)
                 | `Inc, `Pointer _ -> assert false (* Not Done anymore *)
                 | `Cni, `Logic _ -> assert false (* Not Done anymore *)
                 | `Cni, `Pointer _ -> assert false (* Not Done anymore *)
             else acc)
          finfo.li_effects.e_memories acc
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

let make_args ?(uniquify_usual=false) ?parameters f =
  (* From tr_logic_fun_aux *)
  let lab =
    match f.li_labels with [lab] -> lab | _ -> LabelHere
  in
  let params =
    match parameters with
      | None -> f.li_parameters
      | Some params -> params in
  let params = List.map (tparam ~label_in_name:true lab) params in
  let params =
    if uniquify_usual
    then List.map (fun (n,v,ty) -> (n^"_JC"^(id_uniq ()),v,ty)) params
    else params in
  let model_params =
    tr_li_model_args_3 ~label_in_name:true f.li_effects
  in
  let params = params @ model_params in
  let params = List.map (fun (n,_v,ty') -> (n,ty')) params in
  params
(*
let ft_name mem f =
  let mem_name = memory_name mem in
  f.li_final_name^mem_name^ft_suffix

let ftpt_name mem f =
  let mem_name = (memory_name mem)^"_elt" in
  f.li_final_name^mem_name^ft_suffix

let notin_name mem f =
  let mem_name = memory_name mem in
  f.li_final_name^mem_name^notin_suffix
*)

let in_name2 mem f =
  let mem_name = memory_name mem in
  f.li_final_name^mem_name^in_suffix


let mk_tvar a = new term a.vi_type (JCTvar a)

let frame_between_name = "frame_between"

let frame_between ftin notin labels =
  let pid = make_pred frame_between_name in
  pid.li_final_name <- frame_between_name; (* ugly *)
  let var = Common.var (NotIn.jc_ty notin) "a" in
  pid.li_parameters <- [var];
  let ef = {empty_effects with e_memories =
      MemoryMap.add notin.NotIn.mem
        (LogicLabelSet.of_list labels) MemoryMap.empty} in
  pid.li_effects <- ef;
  pid.li_labels <- labels;
  let app = { app_fun = pid;
              app_args = [ftin];
              app_region_assoc = [];
              app_label_assoc = List.combine labels labels} in
  new assertion (JCAapp app)


let compute_predicate_framed () =
  let aux tag (pi, info,params1,params2,kind) =
      test_correct_logic info;
      let params1 = List.map mk_tvar params1 in
      let params2 = List.map mk_tvar params2 in
      let label1,label2 = match pi.li_labels with
        | [label1;label2] -> label1,label2
        | _ -> assert false in
      let mems = info.li_effects.e_memories in
      let apps = MemoryMap.fold
        (fun mem labs acc ->
          let lab = Envset.LogicLabelSet.choose labs in
          let notin = NotIn.from_memory false (mem,lab) in
          let app = app_in_logic info params1 label1 notin in
          let app2 = app_in_logic info params2 label2 notin in
          let app2 = MyBag.make_jc_sub [app2;app] in
          match kind with
            | `Frame ->
              let app1 = frame_between app notin pi.li_labels in
              app2::app1::acc
            | `Sub   -> app2::acc
        ) mems [] in
      let ass = new assertion (JCAand apps) in
      IntHashtblIter.replace Typing.logic_functions_table tag
        (pi,JCAssertion ass) in
  Hashtbl.iter aux Typing.pragma_gen_frame

let user_predicate_code queue id kind pred =
  let (logic,_) = IntHashtblIter.find Typing.logic_functions_table id in
  Options.lprintf "Generate code of %s with %i params@."
    logic.li_name (List.length pred);
  let code = fold_exp (separation_between queue kind) [] pred in
  let lab = match logic.li_labels with
      [lab] -> lab | _ -> LabelHere in
  let trad_code = function
    | `Diff (a,b) ->
      new assertion (JCArelation (mk_tvar a,(`Bneq,`Pointer),mk_tvar b))
    | `In (a,(f,fparams),mem) ->
        let params = List.map mk_tvar fparams in
        (*(make_args ~parameters:fparams f)*)
        let app = app_in_logic f params lab mem in
        let app = MyBag.make_jc_in [mk_tvar a;app] in
        new assertion (JCAnot app)
    | `Disj (((f,fparams),memf),((g,gparams),memg)) ->
      let fparams = List.map mk_tvar fparams in
      let gparams = List.map mk_tvar gparams in
        (*(make_args ~parameters:fparams f)*)
      let fapp = app_in_logic f fparams lab memf in
      let gapp = app_in_logic g gparams lab memg in
      MyBag.make_jc_disj [fapp;gapp] in
  let code = List.map trad_code code in
  let code = new assertion (JCAand code) in
  IntHashtblIter.replace
    Typing.logic_functions_table id (logic,JCAssertion code)

let pragma_gen_sep = Typing.pragma_gen_sep

let predicates_to_generate = Hashtbl.create 10

let compute_needed_predicates () =
  let queue = Queue.create () in
  Hashtbl.iter (fun key (kind,preds) ->
    user_predicate_code queue key kind preds)
    pragma_gen_sep;
  (* use the call graph to add the others needed definitions*)
  while not (Queue.is_empty queue) do
    let (f,((_,mem) as e)) = Queue.pop queue in
    let tag = f.li_tag in
    let l = Hashtbl.find_all predicates_to_generate tag in
    if not (List.mem e l)
    then
      begin
        if MemoryMap.mem mem.NotIn.mem
          f.li_effects.e_memories
        then
          begin
            begin
              match e with
                | `In, mem -> ignore (get_in_logic f mem)
                | `Disj, _ -> ()
            end;
            Hashtbl.add predicates_to_generate tag e;
            (* The user predicate has a particular traitement *)
            if not (Hashtbl.mem pragma_gen_sep f.li_tag) then
              List.iter (fun called -> Queue.add (called,e) queue)
                f.li_calls
          end
      end;
  done;
  compute_predicate_framed ()

(*****)


(*****************************************************************************)
(*                              Logic functions                              *)
(*****************************************************************************)

(* let tr_logic_const vi init acc = *)
(*   let decl = *)
(*     Logic (false, vi.vi_final_name, [],
       tr_base_type vi.vi_type) :: acc *)
(*   in *)
(*     match init with *)
(*       | None -> decl *)
(*       | Some(t,ty) -> *)
(*           let t' = term ~type_safe ~global_assertion:true ~relocate:false
             LabelHere LabelHere t in *)
(*           let vi_ty = vi.vi_type in *)
(*           let t_ty = t#typ in *)
(*           (\* eprintf "logic const: max type = %a@." print_type ty; *\) *)
(*           let pred = *)
(*             LPred ( *)
(*               "eq", *)
(*               [term_coerce Loc.dummy_position ty vi_ty t
                 (LVar vi.vi_name);  *)
(*                term_coerce t#pos ty t_ty t t']) *)
(*           in *)
(*         let ax = *)
(*           Axiom( *)
(*             vi.vi_final_name ^ "_value_axiom", *)
(*             bind_pattern_lets pred *)
(*           ) *)
(*         in *)
(*         ax::decl *)

let fun_def f ta fa ft term_coerce params =
  (* Function definition *)
    match f.li_result_type, ta with
      | None, JCAssertion a -> (* Predicate *)
          let body = fa a in
          [Predicate(false, id_no_loc f.li_final_name,
                     params, body)]
      | Some ty, JCTerm t -> (* Function *)
          let ty' = tr_base_type ty in
          let t' = ft t in
          let t' = term_coerce t#pos ty t#typ t t' in
          if List.mem f f.li_calls then
            let logic = Logic(false, id_no_loc f.li_final_name,
                              params, ty')
            in
            let fstparams = List.map (fun (s,_) -> LVar s) params in
            let app = (LApp(f.li_final_name,fstparams)) in
            let axiom =
              Goal(KAxiom,id_no_loc (jc_axiom^f.li_final_name),
                    make_forall_list params [[LPatT app]]
                      (make_eq app t')) in
            [logic;axiom]
          else
            [Function(false, id_no_loc f.li_final_name,
                      params, ty', t')]
      | ty_opt, (JCNone | JCReads _) -> (* Logic *)
          let ty' = match ty_opt with
            | None -> simple_logic_type prop_type
            | Some ty -> tr_base_type ty
          in
          [Logic(false, id_no_loc f.li_final_name,
                 params, ty')]
      | None, JCInductive l  ->
          [Inductive(false, id_no_loc f.li_final_name,
                     params,
                    List.map
                      (fun (id,_labels,a) ->
                         let ef = Effect.assertion empty_effects a in
                         let a' = fa a in
                         let params =
                           tr_li_model_args_3 ~label_in_name:true ef
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
      |        JCAssertion _ | JCTerm _ | JCInductive _ -> acc
      | JCNone -> acc
      | JCReads pset ->
    let memory_params_reads =
      tr_li_model_mem_args_5 ~label_in_name:true f.li_effects
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
             match f.li_result_type with
               | None ->
                   LImpl(
                     sepa,
                     LIff(
                       LPred(f.li_final_name,normal_params),
                       LPred(f.li_final_name,update_params)))
               | Some _rety ->
                   LImpl(
                     sepa,
                     LPred("eq",[
                             LApp(f.li_final_name,normal_params);
                             LApp(f.li_final_name,update_params)]))
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
             "no_update_" ^ f.li_name ^ "_" ^ string_of_int count
           in
           count + 1, Goal(KAxiom,id_no_loc name,a) :: acc
      ) (0,acc) params)

let gen_no_assign_axioms f ta _fa _ft _term_coerce params acc =
(* TODO: when JCNone, use computed effects instead *)
    match ta with
      | JCAssertion _ | JCTerm _ | JCInductive _ -> acc
      | JCNone -> acc
      | JCReads pset ->
    let memory_params_reads =
      tr_li_model_mem_args_5 ~label_in_name:true f.li_effects
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
           let sepa = LPred ("pset_disjoint", [LVar "tmp"; pset]) in
           let upda =
             LPred ("not_assigns", [LVar "tmpalloc_pre";
                                    LVar "tmpalloc_post";
                                    LVar (fst param);
                                    LVar "tmpmem";
                                    LVar "tmp"])
           in
           let update_params =
             List.map (fun name ->
                         if name = fst param then LVar "tmpmem"
                         else LVar name
                      ) params_names
           in
           let a =
             match f.li_result_type with
               | None ->
                   LImpl (make_and sepa upda,
                     LIff (LPred(f.li_final_name, normal_params),
                           LPred(f.li_final_name, update_params)))
               | Some _rety ->
                   LImpl (make_and sepa upda,
                     LPred ("eq", [LApp (f.li_final_name, normal_params);
                                   LApp (f.li_final_name, update_params)]))
           in
           let a =
             List.fold_left (fun a (name, ty) -> LForall(name, ty, [], a)) a params
           in
           let a =
             LForall ("tmp", raw_pset_type zonety, [],
               LForall ("tmpmem", paramty, [],
                 LForall ("tmpalloc_pre", raw_alloc_table_type zonety, [],
                   LForall ("tmpalloc_post", raw_alloc_table_type zonety, [],
                             a))))
           in
           let name =
             "no_assign_" ^ f.li_name ^ "_" ^ string_of_int count
           in
           count + 1, Goal(KAxiom,id_no_loc name,a) :: acc
      ) (0,acc) params) (* memory_param_reads ? *)

let gen_alloc_extend_axioms f ta _fa _ft _term_coerce params acc =
(* TODO: use computed effects instead*)
    match ta with
      | JCAssertion _ | JCTerm _ | JCInductive _ -> acc
      | JCNone -> acc
      | JCReads ps ->
    let alloc_params_reads =
      tr_li_model_at_args_3 ~label_in_name:true f.li_effects
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
             (collect_pset_locations ~type_safe:false ~global_assertion:true LabelPost)
             ps
         in
         let ps = pset_union_of_list ps in
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
           match f.li_result_type with
             | None ->
                 LImpl(
                   make_and exta valida,
                   LIff(
                     LPred(f.li_final_name,normal_params),
                     LPred(f.li_final_name,update_params)))
             | Some _rety ->
                 LImpl(
                   make_and exta valida,
                   LPred("eq",[
                           LApp(f.li_final_name,normal_params);
                           LApp(f.li_final_name,update_params)]))
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
           "alloc_extend_" ^ f.li_name ^ "_" ^ string_of_int count
         in
         count + 1, Goal(KAxiom,id_no_loc name,a) :: acc
      ) (0,acc) alloc_params_reads)


let reduce f = function
  | [] -> assert false
  | a::l -> List.fold_left f a l

let select_name = "select"

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
    | LLabeled (l, a) -> LLabeled (l, pos a)
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
    | LLabeled (l, a) -> LLabeled (l, neg a)
  and trad f = function
    | LImpl(a,b) -> f (LOr(LNot a,b))
    | LIff(a,b) -> trad f (LAnd (LImpl(a,b),LImpl(b,a)))
    | LIf(_t,_a,_b) -> assert false (* How to trad this? t is a term *)
    | LLet _ -> assert false (* More difficult *)
    | LTrue | LFalse |LAnd _ |LOr _ | LNot _
    | LForall _ | LExists _ | LPred _ | LLabeled _ -> assert false in
  pos e

(*module Def_ft_pred :
sig  val def_ft_pred : for_one:bool -> 'a ->
       NotIn.t ->
       Output.why_decl list -> Output.why_decl list -> Output.why_decl list
     val ft_name : NotIn.t -> string -> string
     val ft_name_elt : NotIn.t -> string -> string
     val ft_for_ft : Fenv.logic_info ->
       (string * Output.logic_type) list ->
       NotIn.t ->
       (Fenv.logic_info * (string * 'e) list) list ->
       Output.why_decl list -> Output.why_decl list
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
      | TLet _ -> assert false

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

  let rec def_ft_pred ~for_one _f notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai
           transformation d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,params,l)] -> begin
          let params = List.map (fun (s,ty) -> ("_JC_"^s,ty)) params in
          let name = ft_name notin f_name in
          Options.lprintf "Generate logic ft : %s :@." name;
          let acc = Logic(false,
                          name,
                          add_decl_args notin params,
                          simple_logic_type prop_type)::acc in

          let rec gen_one_neg acc = function
            | LNot _a -> assert false (*gen_one_neg notin acc a*)
            | LPred (_id,lt) as e ->
                (*Options.lprintf "term_extract_effect %s@." id;*)
                let acc = List.fold_left
                  (term_extract_effect notin) acc lt in
                (trad_pred notin e)::acc
            | LNamed (_,a) -> gen_one_neg acc a
            | LAnd (a,b) ->
                gen_one_neg (gen_one_neg acc b) a
            | _ -> assert false in
          let rec gen_one_pos ~impl acc = function
            | LNamed (_,a) -> gen_one_pos ~impl acc a
            | LPred (s,lt) -> (* Normalement le predicat inductif défini *)
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

          (*let acc =
            if not for_one
            then generic_axiom_for_ft ~do_rem f_name notin params acc
            else acc in*)
          let acc = List.fold_left
            (fun acc (ident,assertion) ->
               let axiom_name =
                 "axiom"^"_ft_"^(NotIn.mem_name2 notin)^f_name^ident in
               Options.lprintf "Generate axiom ft : %s :@." axiom_name;
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
          Options.lprintf "Generate logic ft : %s :@." name;
          let new_pred = Predicate (bool,
                                    name,
                                    add_decl_args notin params,
                                    conv_to_ft notin assertion) in
          new_pred::acc
      | [Function (_bool,f_name,params,_ltype,term)] ->
          let name = ft_name notin f_name in
          Options.lprintf "Generate logic ft: %s :@." name;
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
          Options.lprintf "Generate axiom ft: %s :@." axiom_name;
          let asser = gen_one [] term in
          let asser = make_equiv asser
            (conv_app_pred notin f_name
               (List.map (fun (x,_) -> LVar x) params)) in
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
          def_ft_pred ~for_one _f notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          (Pp.print_list Pp.newline fprintf_why_decl) ta_conv;acc


  let ft_for_ft f args notin framed acc =
    let conjs = List.map
      (fun (f,params) ->
         (conv_app_pred notin f.li_name
            (List.map (fun (x,_) -> LVar x) params)))
      framed in
    let code = make_and_list conjs in
    let args = add_decl_args notin args in
    let ft_name = ft_name notin f.li_name in
    Predicate(false,ft_name,args,code)::acc
end
*)

(* Memory merging.                                                                                  *)
(* This is sometimes needed when we have a pointer to an hroot structure passed as a parameter to a *)
(* logic function (predicate).                                                                      *)
(* The pointer can potentially reference several memories, but its often                            *)
(* the case that it can't reference every such memory in the context of the same axiom.             *)
(* So it's very inefficient (and sometimes incorrect) to pass all these memories to such a function *)
(* each time. The simple solution we use is a number of polymorphic memories.                       *)
(* Here we apply a heuristic: we only pass the greatest number of memories                          *)
(* counted as effects in either of the involved axioms.                                             *)
let tr_logic_model_params f =
  let open Typing in
  let module List = ListLabels in
  let module LabelRegionMap = PairRegionMap (LogicLabelOrd) (PairOrd (LogicLabelOrd) (InternalRegion)) in
  Lazy.force @@
  let open Option in
  let tr_li_model_args_3 = tr_li_model_args_3 ~label_in_name:true in
  let abort_on cond l = if cond l then abort else (return l) in
  value ~default:(lazy (tr_li_model_args_3 f.li_effects)) @@
  begin
    (poly_mem_regions f |>
     abort_on ((=) []))
    >>= fun regions ->
    MemoryMap.partition
      (fun (_, r) _ -> List.exists regions ~f:(Region.equal r))
      f.li_effects.e_memories
    |>
    fun (replace, _ as r) ->
    abort_on (Fn.const @@ MemoryMap.is_empty replace) r
    >>= fun (replace, keep) ->
    (try
       Option.map (StringHashtblIter.find axiomatics_table) f.li_axiomatic
     with
     | Not_found -> abort)
    >>= fun ax_data ->
    List.filter ax_data.axiomatics_decls
      ~f:(fun (ABaxiom (_, _, _, a)) -> List.hd (occurrences [f.li_tag] a) <> [])
    |>
    abort_on ((=) [])
    >>= fun ax_decls ->
    List.map ax_decls
      ~f:(fun decl ->
        let decl = restrict_poly_mems_in_axiomatic_decl MemoryMap.empty decl in
        let ef = axiomatic_decl_effect empty_effects decl in
        li_effects_from_ax_decl f ef empty_effects decl)
    |>
    let count mm =
      LabelRegionMap.(
        MemoryMap.fold
          (fun (_, r) ls lrm ->
             if List.exists regions ~f:(Region.equal r) then
               LogicLabelSet.fold
                 (fun l lrm ->
                    let key = l, r in
                    let c = find_or_default key 0 lrm in
                    add key (c + 1) lrm)
                 ls
                 lrm
             else
               lrm)
          mm
          empty)
    in
    List.map ~f:(fun { e_memories = mm } -> count mm) %>
    List.fold_left ~init:LabelRegionMap.empty ~f:(LabelRegionMap.merge max) %>
    fun maxs -> abort_on (Fn.const (LabelRegionMap.compare (-) (count replace) maxs <= 0)) maxs
      >>= fun maxs ->
      LabelRegionMap.bindings maxs
      |>
      List.mapi
        ~f:(fun i ((l, r), c) ->
          let poly_name i = "poly_" ^ string_of_int i ^ "_" ^ Region.name r in
          let name = lvar_name ~label_in_name:true l % poly_name in
          let var = lvar ~label_in_name:true ~constant:true l % poly_name in
          let typ j =
            let ri =
              match r.r_type with
              | JCTpointer (JCtag ({ si_root = Some ri }, _), _, _)
              | JCTpointer (JCroot ri, _, _) -> ri
              | _ -> failwith "unexpected region type in memory merging"
            in
            raw_memory_type (root_model_type ri) (logic_type_var @@ "a" ^ string_of_int i ^ "_" ^ string_of_int j)
          in
          List.map ~f:(fdup3 name var typ) @@ Stdlib.List.range 0 `To (c - 1))
      |>
      List.flatten |>
      fun poly_params ->
      let initial_params = tr_li_model_args_3  { f.li_effects with
                                                 e_memories = keep;
                                                 e_globals = VarMap.empty }
      in
      let final_params = tr_li_model_args_3 { empty_effects with
                                              e_globals = f.li_effects.e_globals }
      in
      return @@ lazy (initial_params @ poly_params @ final_params)
  end




(*
module Def_in :
sig  val def_in : 'a ->  NotIn.t ->
       Output.why_decl list -> Output.why_decl list ->
       Fenv.logic_info * NotIn.t
       -> Output.why_decl list
     val def_disj : string -> bool -> (string * Output.logic_type) list ->
       Output.why_decl list -> NotIn.t  -> Output.why_decl list
     val def_frame_in :
        string -> NotIn.t ->
       (string * Output.logic_type) list ->
       Output.why_decl list -> NotIn.t -> Output.why_decl list
     val notin_for_notin :  Fenv.logic_info ->
       (string * Output.logic_type) list ->
       NotIn.t ->
       Fenv.logic_info * NotIn.t ->
       (Fenv.logic_info * (string * 'n) list) list ->
       Output.why_decl list -> Output.why_decl list

end
  =
struct

  let notin_name notin s = s^(NotIn.mem_name2 notin)^in_suffix
  (* let gen_ft_name notin s = s^(NotIn.mem_name2 notin)^ft_suffix *)
  (* let gen_ft_name_elt notin s = s^(NotIn.mem_name2 notin)^"_elt"^ft_suffix
   *)

  let conv_app_pred var_in notin s lt =
    let notin_name = notin_name notin s in
    LPred(disj_name,[LApp (notin_name,lt);var_in])

  let conv_app_pred_pt var_in elt =
    LNot (LPred(in_pred,[elt;var_in]))

  let trad_app var_in notin e =
    match e with
      | LApp (s,[memory;elt]) when s = select_name ->
          if NotIn.is_memory_var notin memory
          then conv_app_pred_pt var_in elt
          else LTrue
      | LApp (s,_) when s = select_name ->  assert false (*really impossible*)
      | LApp (s,lt) ->
          if List.exists (NotIn.is_memory_var notin) lt
          then conv_app_pred var_in notin s lt
          else LTrue
      | _ -> assert false

  let trad_pred ft notin e =
    match e with
      | LPred (s,lt) ->
          if List.exists (NotIn.is_memory_var notin) lt
          then conv_app_pred ft notin s lt
          else LTrue
      | _ -> assert false

  let rec term_extract_effect notin acc e =
    match e with
      | LConst _ | LVar _ | LVarAtLabel _ -> acc
      | Tnamed (_,t) -> term_extract_effect notin acc t
      | LApp (_,lt) -> (trad_app notin e)::
          (List.fold_left (term_extract_effect notin) acc lt)
      | TIf _ -> assert false
      | TLet _ -> assert false

  let gen axiom_name f_name gen_framed notin_update params framed_params =
    let elt = "elt"^tmp_suffix in
    let elt_val = "elt_val"^tmp_suffix in
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
    let a,trig =
      match gen_framed with
        | `Pred gen_framed ->
            let pred_normal = gen_framed framed_normal_params in
            let pred_update = gen_framed framed_update_params in
            LImpl(pred_normal,pred_update),LPatP pred_update
        | `Term gen_framed ->
            let term_normal = gen_framed framed_normal_params in
            let term_update = gen_framed framed_update_params in
            make_eq term_normal term_update, LPatT term_update in
    let a = LImpl(sepa,a) in
    let a = make_forall_list framed_params [[trig]] a in
    let a = LForall (elt,NotIn.ty_elt notin_update,[],
                     LForall (elt_val,NotIn.ty_elt_val notin_update,[],a)) in
    let axiom_name = "axiom"^"_no_update_"^axiom_name^
      (NotIn.mem_name notin_update) in
    Axiom(axiom_name,a)

  (*let def_no_update f_name notin_update params prop =
    gen f_name f_name prop notin_update params []*)
(*
  let def_frame_ft f_name notin params acc notin_update =
    let ft_name = Def_ft_pred.ft_name notin f_name in
    let p = (NotIn.name notin,NotIn.ty notin) in
    let gen_framed params = LPred(ft_name,params) in
    (gen ft_name f_name (`Pred gen_framed) notin_update params
       (p::params))::acc

  let def_frame_ft_elt f_name notin params  acc notin_update =
    let ft_name = Def_ft_pred.ft_name_elt notin f_name in
    let p = ("p"^tmp_suffix,NotIn.ty_elt notin) in
    let gen_framed params = LPred(ft_name,params) in
    let ax = gen ft_name f_name (`Pred gen_framed) notin_update params
      (p::params) in
    ax::acc
*)
  let def_frame_notin f_name notin params acc notin_update =
    let notin_name = notin_name notin f_name in
    let gen_framed params = LApp(notin_name,params) in
    (gen notin_name f_name (`Term gen_framed) notin_update params params)::acc

  let def_frame f_name is_pred params acc notin_update =
    let gen_framed =
      if is_pred
      then `Pred (fun params -> LPred(f_name,params))
      else `Term (fun params -> LApp(f_name,params)) in
    (gen f_name f_name gen_framed notin_update params params)::acc
(*
  let gen_frame2 (f_name,notin,params) (ft_name,ft_notin,ft_params)
      acc (notin_notin_update, ft_notin_update) =
    let forall_params = remove_double Pervasives.compare
      (ft_params @ params) in
    let params = List.map fst params in
    let ft_params = List.map fst ft_params in
    let elt = "elt"^tmp_suffix in
    let elt_val = "elt_val"^tmp_suffix in
    let notin_update =
      match notin_notin_update, ft_notin_update with
        | None, None -> assert false
        | Some m, None | None, Some m -> m
        | Some m1, Some m2 ->
            assert (NotIn.mem_name m1 = NotIn.mem_name m2);
            assert (NotIn.ty_elt m1 = NotIn.ty_elt m2);
            assert (NotIn.ty_elt_val m1 = NotIn.ty_elt_val m2);
            m1 in
    let to_update =
      List.map (fun name ->
                  if name = NotIn.mem_name notin_update then
                    LApp("store",[LVar name;LVar elt;LVar elt_val])
                  else LVar name) in
    let params_update = to_update params in
    let ft_params_update = to_update ft_params in
    let params = List.map make_var params in
    let ft_params = List.map make_var ft_params in
    let sepa notin_update f_name params =
      match notin_update with
        | Some notin_update ->
            MyBag.make_in (LVar elt)
              (LApp ((notin_name notin_update f_name),params))
        | None -> LTrue in
    let notin_notin_update_sepa =
      sepa notin_notin_update f_name params in
    let ft_notin_update_sepa =
      sepa ft_notin_update ft_name ft_params in
    let body = conv_app_pred (ft_name,ft_notin,ft_params)
      notin f_name params in
    let body_update = conv_app_pred (ft_name,ft_notin,ft_params_update)
      notin f_name params_update in
    let body =
      make_impl notin_notin_update_sepa
        (make_impl ft_notin_update_sepa
           (make_impl body body_update)) in
    let body = make_forall_list forall_params [[LPatP body_update]] body in
    let body =
      LForall (elt,NotIn.ty_elt notin_update,[],
               LForall (elt_val,NotIn.ty_elt_val notin_update,[],body)) in
    let axiom_name = "axiom"^"_no_update_ftn_"^ft_name^f_name^
      (NotIn.mem_name notin_update)^(id_uniq ()) in
    Axiom(axiom_name,body)::acc

  let def_frame_ft_notin (f_name,notin,params) (ft,ft_notin) acc
      notin_notin_updates =
    (** which notin *)
    let ft_notin_updates =
      let todos =
        Hashtbl.find_all predicates_to_generate ft.li_tag in
      let filter_notin acc = function
        | ((`Notin _| `Notin_pt) , mem) -> (NotIn.from_memory false mem)::acc
        | _ -> acc in
      (* notin_updates is used to create the frames axioms *)
      List.fold_left filter_notin [] todos in
    let of_list =
      List.fold_left (fun m x ->NotInMap.add x x m) NotInMap.empty in
    let notin_updates =
      NotInSet.union
        (NotInSet.of_list notin_notin_updates)
        (NotInSet.of_list ft_notin_updates) in
    let notin_notin_updates = of_list notin_notin_updates in
    let ft_notin_updates = of_list ft_notin_updates in
    let add notin acc =
      ((try Some (NotInMap.find notin notin_notin_updates)
      with Not_found -> None),
      (try Some (NotInMap.find notin ft_notin_updates)
      with Not_found -> None))::acc in
    let notin_updates = NotInSet.fold add notin_updates [] in
    (** params *)
    let ft_name = ft.li_name in
    let ft_params_usual,ft_params_model = tr_params_usual_model_aux ft in
    let ft_params_usual =
      List.map (fun (x,ty) -> "_JC_ft_"^x,ty)  ft_params_usual in
    let ft_params_model = List.map (fun (x,ty) -> x,ty)
      ft_params_model in
    let ft_params = ft_params_usual @ ft_params_model in
    let ft = (ft_name,ft_notin,ft_params) in
    List.fold_left (gen_frame2 (f_name,notin,params) ft) acc notin_updates
*)
  let rec def_notin _f notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai transformation
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
          let rec gen_one_pos ~impl notin acc = function
            | LNamed (_,a) -> gen_one_pos ~impl notin acc a
            | LPred (s,lt) ->
                (* Normalement le predicat inductif défini *)
                let asser = make_and_list acc in
                impl notin s lt asser
            | _ -> assert false in
          let rec gen_one ~impl notin acc = function
            | LForall(s,ty,tr,a) ->
                LForall(s,ty,tr,gen_one ~impl notin acc a)
            | LImpl (a1,a2) ->
                let acc = gen_one_neg notin acc a1 in
                make_impl a1 (gen_one ~impl notin acc a2)
            | LNamed (_,a) -> gen_one ~impl notin acc a
            | (LAnd _ | LOr _) -> assert false
            | a -> gen_one_pos ~impl notin acc a in

          let name = (notin_name notin f_name) in
          Options.lprintf "Generate logic notin : %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in
          let acc = List.fold_left
            (fun acc (ident,assertion) ->
               let impl notin s lt asser =
                 make_impl (conv_app_pred ft notin s lt) asser in
               let asser = gen_one ~impl notin [] assertion in
               let asser = make_forall_list ft_params_usual [] asser in
               let axiom_name =
                 "axiom"^"_notin_"^(NotIn.mem_name notin) ^ident^f_name in
                 Options.lprintf "Generate axiom notin : %s@." axiom_name;
               (*let asser = LForall (NotIn.name notin,
                                    NotIn.ty notin ,[],asser) in*)
               let asser = Axiom (axiom_name,asser) in
               asser::acc
            ) acc l in
          (* The other side *)
          let params = List.map (fun (s,ty) -> ("_JC_"^s,ty)) params in
          let conjs = List.map
            (fun (_ident,assertion) ->
               let impl _ _s lt asser =
                 let eqs = List.map2
                   (fun (x,_) y -> make_eq (LVar x) y) params lt in
                 make_impl (make_and_list eqs) asser in
               gen_one ~impl notin [] assertion) l in
          let conjs = make_and_list conjs in
          let ft_params_model = List.map (fun (x,ty) -> "_JC_"^x,ty)
            ft_params_model in
          let ft = (ft_name,ft_notin,
                    List.map (fun (x,_) -> LVar x)
                      (ft_params_usual @ ft_params_model)) in
          let conclu = conv_app_pred ft notin f_name
            (List.map (fun (x,_) -> LVar x) params) in
          let asser = make_impl conjs conclu in
          (*let forall_params = remove_double Pervasives.compare
            (ft_params_usual @ ft_params_model @ params) in*)
          let forall_params = ft_params_usual @ params in
          let asser = make_forall_list forall_params [[LPatP conclu]] asser in
          let axiom_name = "axiom"^"_notin_"^(NotIn.mem_name2 notin)^f_name in
          let asser = Axiom (axiom_name,asser) in
          asser::acc
        end
      | [Predicate (_,f_name,params,assertion)] ->
          let name = (gen_ft_name ft_notin ft_name) ^
            (notin_name notin f_name) in
          Options.lprintf "Generate logic notin (pred): %s :@." name;
          let rec gen_one_neg notin acc = function
            | LNot _a -> assert false (*gen_one_neg notin acc a*)
            | LPred (_,lt) as e ->
                let acc = List.fold_left
                  (term_extract_effect ft notin) acc lt in
                (trad_pred ft notin e)::acc
            | LNamed (_,a) -> gen_one_neg notin acc a
            | LAnd (a,b) ->
                gen_one_neg notin (gen_one_neg notin acc b) a
            | _ -> assert false in
          let asser = gen_one_neg notin [] assertion in
          let asser = make_and_list asser in
          let lt = List.map (fun (x,_) -> LVar x) params in
          let asser = make_impl (conv_app_pred ft notin f_name lt) asser in
          let asser = make_forall_list params [] asser in
          let new_pred = Axiom (name,make_forall_list
                                  ft_params_usual [] asser) in
          new_pred::acc
      | [Function (_bool,f_name,params,_ltype,term)] ->
          let name = (gen_ft_name ft_notin ft_name)
            ^ (notin_name notin f_name) in
          Options.lprintf "Generate logic notin (fun): %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in
          let rec gen_one acc term =
              match term with
                | TIf(_if,_then,_else) ->
                    let acc = term_extract_effect ft notin acc _if in
                    LIf(_if,gen_one acc _then,gen_one acc _else)
                | e ->
                    let acc = term_extract_effect ft notin acc e in
                    let acc = make_and_list acc in
                    acc in
          let axiom_name = "axiom"^"_notin_"^(NotIn.mem_name2 notin)^f_name in
          Options.lprintf "Generate axiom notin : %s :@." axiom_name;
          let asser = gen_one [] term in
          let conclu = conv_app_pred ft notin f_name
            (List.map (fun (x,_) -> LVar x) params) in
          let asser = make_equiv asser conclu in
          let par = params in
          let asser = make_forall_list par [] asser in
          let asser = make_forall_list  ft_params_usual [] asser in
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
          def_notin _f notin ta_conv acc ft_o
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          (Pp.print_list Pp.newline fprintf_why_decl) ta_conv;acc

  let rec def_notin_logic notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai transformation
           d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,params,_)] -> begin
          let name = notin_name notin f_name in
          Options.lprintf "Generate logic notin : %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in
          acc
        end
      | [Predicate (_,f_name,params,_)] ->
          let name = notin_name notin f_name in
          Options.lprintf "Generate logic notin : %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in
          acc
      | [Function (_bool,f_name,params,_ltype,_)] ->
          let name = notin_name notin f_name in
          Options.lprintf "Generate logic notin: %s :@." name;
          let acc = Logic(false,
                          name,
                          params,
                          NotIn.ty notin)::acc in
          acc
      | [Logic(_bool,f_name,params,_ltype);
         Axiom(_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          def_notin_logic notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          (Pp.print_list Pp.newline fprintf_why_decl) ta_conv;acc

  let notin_for_notin f args notin (ft,ft_notin) framed acc =
    let ft_name = ft.li_name in
    let ft_params_usual,ft_params_model = tr_params_usual_model_aux ft in
    let ft_params_usual =
      List.map (fun (x,ty) -> "_JC_ft_"^x,ty)  ft_params_usual in
    let ft_params_model = List.map (fun (x,ty) -> x,ty) ft_params_model in
    let ft = (ft_name,ft_notin,
              List.map (fun (x,_) -> LVar x)
                (ft_params_usual @ ft_params_model)) in
    let name = (notin_name notin f.li_name) in
    Options.lprintf "Generate logic notin_notin : %s :@." name;
    let acc = Logic(false,
                    name,
                    args,
                    NotIn.ty notin)::acc in
    let axiom_name = "axiom"^"_notin_"^(NotIn.mem_name2 notin)
      ^f.li_name in
    Options.lprintf "Generate axiom notin : %s :@." axiom_name;
    let conjs = List.map
      (fun (f,params) ->
         (conv_app_pred ft notin f.li_name
            (List.map (fun (x,_) -> LVar x) params)))
      framed in
    let code = make_and_list conjs in
    let conclu = conv_app_pred ft notin f.li_name
      (List.map (fun (x,_) -> LVar x) args) in
    let asser = make_equiv code conclu in
    let asser = make_forall_list args [] asser in
    let asser = make_forall_list  ft_params_usual [] asser in
    let asser = Axiom (axiom_name,asser) in
    asser::acc


end
*)

module InDisj :
sig

  type define = NotIn.t -> why_decl list -> why_decl list -> why_decl list

  val define_In    : define
  val define_disj  : define
  val define_frame_between : define
  val define_x_sub : define
  val define_sub_x : define
  val define_sub   : define

  val def_frame_in :  string -> NotIn.t -> (string * logic_type) list ->
    why_decl list -> NotIn.t list -> why_decl list
  val def_frame : string -> bool -> string ->
    (string * logic_type) list ->
    why_decl list -> NotIn.t list -> why_decl list

  type for_in = string -> (string * logic_type) list ->
    NotIn.t -> (Fenv.logic_info * (string * logic_type) list) list ->
    why_decl list -> why_decl list

  val in_for_in    : for_in
  val disj_for_in  : for_in
  val x_sub_for_in : for_in
  val sub_x_for_in : for_in

end =
struct

  type define =
    NotIn.t ->
    why_decl list ->
    why_decl list -> why_decl list

  type for_in =
    string -> (string * logic_type) list ->
    NotIn.t -> (Fenv.logic_info * (string * logic_type) list) list ->
    why_decl list -> why_decl list


  let trad_app s lt = (s,lt)

  let rec term_extract_application acc e =
    match e with
      | LConst _ | LVar _ | LDeref _ | LDerefAtLabel _ -> acc
      | TLabeled (_, t) -> term_extract_application acc t
      | LApp (s,lt) -> (trad_app s lt)::
          (List.fold_left term_extract_application acc lt)
      | TIf _ -> assert false
      | TLet _ -> assert false

  let pred_extract_effect s lt acc =
    (trad_app s lt)::(List.fold_left term_extract_application acc lt)

  let inductive_extract_effect ass =
    let rec iee e acc =
      match e with
        | LTrue | LFalse -> acc
        | LImpl(f1,f2) -> (iee f2) (neg f1 acc)
        | LPred(_) -> acc
        | _ -> failwith "Inductive must be forall x,.. Pn -> ... -> P1"
    and neg e acc =
      match e with
        | LTrue | LFalse -> acc
        | LAnd (f1,f2) -> neg f1 (neg f2 acc)
        | LPred(s,lt) -> pred_extract_effect s lt acc
        | _ -> failwith "Inductive must be forall x,.. (Pn && Pj) -> ... -> P1"
    and rq = function
        | LForall (_,_,_,f) -> rq f
        | e -> iee e [] in
    let effects = rq ass in
    remove_double Pervasives.compare effects

  let rec rewrite_inductive_case rw = function
    | LForall (s,ty,_,f) -> LForall(s,ty,[],rewrite_inductive_case rw f)
    | LTrue | LFalse as e -> e
    | LImpl(f1,f2) -> LImpl(f1,rewrite_inductive_case rw f2)
    | LPred(s,lt) -> rw s lt
    | _ -> failwith "Inductive must be forall x,.. Pn -> ... -> P1"


  let rec term_interp_or interp t =
    let fnT = term_interp_or interp in
    match t with
      | TIf(if_,then_,else_) ->
        LIf(if_,make_or (fnT if_) (fnT then_),
            make_or (fnT if_) (fnT else_))
      | LConst _ -> LFalse
      | LApp (s,lt) -> List.fold_left (fun acc e -> make_or acc (fnT e))
        (interp s lt) lt
      | LVar _ -> LFalse
      | TLabeled (_,t) -> term_interp_or interp t
      | LDerefAtLabel _ ->
        failwith "Not implemented, how to do that? Show me the example!!! thx"
      | _ -> failwith "Not implemented"

  let rec term_interp_and interp t =
    let fnT = term_interp_and interp in
    match t with
      | TIf(if_,then_,else_) ->
        LIf(if_,make_and (fnT if_) (fnT then_),
            make_and (fnT if_) (fnT else_))
      | LConst _ -> LTrue
      | LApp (s,lt) -> List.fold_left (fun acc e -> make_and acc (fnT e))
        (interp s lt) lt
      | LVar _ -> LTrue
      | TLabeled (_,t) -> term_interp_and interp t
      | LDerefAtLabel _ ->
        failwith "Not implemented, how to do that? Show me the example!!! thx"
      | _ -> failwith "Not implemented"

  let rec pred_interp_or interp e =
    let fnT = term_interp_or interp in
    let fnF = pred_interp_or interp in
    match e with
    | LTrue | LFalse -> LFalse
    | LAnd(f1,f2) -> make_or (fnF f1) (fnF f2)
    | LOr(f1,f2) -> make_or (make_and f1 (fnF f1)) (make_and f2 (fnF f2))
    | LForall (s,lt,_,f) -> LExists(s,lt,[],fnF f)
    | LExists (s,lt,_,f) -> LExists(s,lt,[],make_and f (fnF f))
    | LPred(s,lt) -> List.fold_left (fun acc e -> make_or acc (fnT e))
        (interp s lt) lt
    | _ -> failwith "Not Implemented, not in formula"


  let rec pred_interp_and interp e =
    let fnT = term_interp_and interp in
    let fnF = pred_interp_and interp in
    match e with
    | LTrue | LFalse -> LTrue
    | LAnd(f1,f2) -> make_and (fnF f1) (fnF f2)
    | LOr(f1,f2) -> make_and (make_impl f1 (fnF f1)) (make_impl f2 (fnF f2))
    | LForall (s,lt,_,f) -> LForall(s,lt,[],fnF f)
    | LExists (s,lt,_,f) -> LForall(s,lt,[],make_impl f (fnF f))
    | LPred(s,lt) -> List.fold_left (fun acc e -> LAnd(acc,fnT e))
        (interp s lt) lt
    | _ -> failwith "Not Implemented, not in formula"

  let in_interp_app var notin s lt =
    if s = select_name then
      match lt with
        | [_;p] -> make_eq (LVar (fst var)) p
        | _ -> assert false
    else
    LPred(in_pred,[LVar (fst var);LApp(in_name notin s, lt)])

  let disj_interp_app var notin s lt =
    if s = select_name then
      match lt with
        | [_;p] -> LNot (LPred(in_pred,[p;LVar (fst var)]))
        | _ -> assert false
    else
    LPred(disj_pred,[LVar (fst var);LApp(in_name notin s, lt)])

  let frame_between_interp_app var_mem notin s lt =
    assert (s <> select_name);
    LPred(frame_between_name, [LApp(in_name notin s, lt);
                               LVar (fst var_mem);
                               LVar (NotIn.mem_name notin)])

  let sub_interp_app x1 notin x2 =
    match x1,x2 with
      | `Var var1,`Var var2 -> LPred(sub_pred,[LVar (fst var1);
                                               LVar (fst var2)])
      (* This case must be in fact var1 is a singleton *)
      | `Var _, `App (s,[_;_]) when s = select_name -> assert false
      | `App (s,[_;p]), `Var var when s = select_name ->
        LPred(in_pred,[p;LVar (fst var)])
      | `Var var, `App (s,lt) ->
        LPred(sub_pred,[LVar (fst var);LApp(in_name notin s, lt)])
      | `App (s,lt), `Var var ->
        LPred(sub_pred,[LApp(in_name notin s, lt);LVar (fst var)])
      (* two app *)
      | `App(s1,[_;p1]), `App(s2,[_;p2])
        when s1 = select_name && s2 = select_name ->
        make_eq p1 p2
      (* This case must be in fact app2 is a singleton *)
      | `App _, `App(s2,[_;_]) when s2 = select_name -> assert false
      | `App(s1,[_;p1]), `App(s2,lt2) when s1 = select_name ->
        LPred(in_pred,[p1;LApp(in_name notin s2, lt2)])
      | `App(s1,lt1), `App(s2,lt2) ->
        LPred(sub_pred,[LApp(in_name notin s1,lt1);LApp(in_name notin s2,lt2)])

  let mem_are_compatible notin (_,lt) =
    List.exists (NotIn.is_memory_var notin) lt
(*
  let inductive_to_axioms name (pname,var,fname,lt) l acc =
    let constr acc (ident,assertion) =
      Axiom (name^fname^ident,assertion)::acc in
    let acc = List.fold_left constr acc l in
    let var = ((fst var)^tmp_suffix,snd var) in
    let lt = List.map (fun (s,ty) -> (s^tmp_suffix,ty)) lt in
    let rec rewrite = function
      | LForall(v,t,_,a) -> LExists(v,t,[],rewrite a)
      | LImpl(f1,f2) -> LAnd(f1,rewrite f2)
      | LPred(_,[var2;LApp(_,lt2)]) ->
        let eqs = (var,var2) :: (List.combine lt lt2) in
        let eqs = List.map (fun (a1,a2) -> make_eq (LVar (fst a1)) a2) eqs in
        make_and_list eqs
      | _ -> assert false in
    let assertions = List.map (fun (_,a) -> rewrite a) l in
    let assertions = make_or_list assertions in
    let pred = LPred(pname,
                     [LVar (fst var);
                      LApp(fname,List.map (fun var -> LVar (fst var)) lt)]) in
    let assertion = LImpl(pred,assertions) in
    let assertion = make_forall_list (var::lt) [] assertion in
    Axiom ("axiom_"^name^pname^"_"^fname,assertion) :: acc
    *)
  let match_pred p1 p2 =
    match p1,p2 with
      | LPred(s1,lt1), LPred(s2,lt2) when s1 = s2 ->
        List.fold_left2 match_term [] lt1 lt2
      | _ -> invalid_arg "match_pred p1 is not a valid context for p2"

  (* bindvars must be fresh variables... *)
  let inductive_to_axioms name pred bindvars l acc =
    let constr acc (ident,assertion) =
      Goal(KAxiom,id_no_loc (name^ident),assertion)::acc in
    let acc = List.fold_left constr acc l in
    let rec rewrite = function
      | LForall(v,t,_,a) -> LExists(v,t,[],rewrite a)
      | LImpl(f1,f2) -> LAnd(f1,rewrite f2)
      | LPred _ as p2 ->
        let eqs = match_pred pred p2 in
        let eqs = List.map (fun (a1,a2) -> make_eq (LVar a1) a2) eqs in
        make_and_list eqs
      | _ -> assert false in
    let assertions = List.map (fun (_,a) -> rewrite a) l in
    let assertions = make_or_list assertions in
    let assertion = LImpl(pred,assertions) in
    let assertion = make_forall_list bindvars [] assertion in
    Goal(KAxiom,id_no_loc ("axiom_"^name),assertion) :: acc


  let rec define_In notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai transformation
           d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,params,l)] ->
        let name = (in_name notin f_name.why_name) in
        Options.lprintf "Define logic in : %s :@." name;
        (* let acc = Logic(false, name, params, NotIn.ty notin)::acc in *)
        let var = ("jc_var",NotIn.ty_elt notin) in
        let gen_case acc (ident,assertion) =
          let effects = inductive_extract_effect assertion in
          let effects = List.filter (mem_are_compatible notin) effects in
          let rw seff lteff s lt =
            LImpl(in_interp_app var notin seff lteff,
                  in_interp_app var notin s lt) in
          let nb = ref 0 in
          let rewrite acc (seff,lteff) =
            incr nb;
            let assertion =
              LForall(fst var,snd var,[],
                      rewrite_inductive_case (rw seff lteff) assertion) in
            (ident^(string_of_int !nb), assertion) :: acc in
          List.fold_left rewrite acc effects in
        let l = List.fold_left gen_case [] l in
        let var = ((fst var)^tmp_suffix,snd var) in
        let lt = List.map (fun (s,ty) -> (s^tmp_suffix,ty)) params in
        let pred = in_interp_app var notin f_name.why_name
          (List.map (fun x -> LVar (fst x)) lt) in
          inductive_to_axioms ("In"^name) pred (var::lt) l acc
      | [Function (_,f_name,params,_,term)] ->
          let name = in_name notin f_name.why_name in
          Options.lprintf "Generate logic notin (fun): %s :@." name;
          let acc = Logic(false,
                          {f_name with why_name = name},
                          params,
                          NotIn.ty notin)::acc in
          let axiom_name = "axiom"^"_in_"^(NotIn.mem_name2 notin)^f_name.why_name in
          Options.lprintf "Generate axiom notin : %s :@." axiom_name;
          let var = ("jc_var",NotIn.ty_elt notin) in
          let interp s lt =
            if mem_are_compatible notin (s,lt)
            then in_interp_app var notin s lt
            else LFalse in
          let asser = term_interp_or interp term in
          let conclu = in_interp_app var notin f_name.why_name
            (List.map (fun (x,_) -> LVar x) params) in
          let asser = make_equiv asser conclu in
          let params = var::params in
          let asser = make_forall_list params [] asser in
          let asser = Goal(KAxiom,id_no_loc axiom_name,asser) in
          asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Goal(KAxiom,_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          define_In notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv; assert false

  let rec define_disj notin ta_conv acc =
    match ta_conv with
      (* Devrait peut-être utiliser la vrai transformation
         d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,params,l)] ->
        let name = (in_name notin f_name.why_name) in
        let var = ("jc_var",NotIn.ty notin) in
        let gen_case acc (ident,assertion) =
          let effects = inductive_extract_effect assertion in
          let effects = List.filter (mem_are_compatible notin) effects in
          let rw s lt =
            List.fold_left (fun acc (seff,lteff) ->
              LImpl(disj_interp_app var notin seff lteff,acc))
              (disj_interp_app var notin s lt) effects in
          let rewrite acc =
            let assertion =
              LForall(fst var,snd var,[],
                      rewrite_inductive_case rw assertion) in
            (ident, assertion) :: acc in
          rewrite acc in
        let l = List.fold_left gen_case [] l in
        let var = ((fst var)^tmp_suffix,snd var) in
        let lt = List.map (fun (s,ty) -> (s^tmp_suffix,ty)) params in
        let pred = disj_interp_app var notin f_name.why_name
          (List.map (fun s -> LVar (fst s)) lt) in
        inductive_to_axioms ("disj"^name) pred (var::lt) l acc
      | [Function (_,f_name,params,_,term)] ->
        let axiom_name = "axiom"^"_disj_"^(NotIn.mem_name2 notin)^f_name.why_name in
        Options.lprintf "Generate axiom disj : %s :@." axiom_name;
        let var = ("jc_var",NotIn.ty notin) in
        let interp s lt =
          if mem_are_compatible notin (s,lt)
          then disj_interp_app var notin s lt
          else LTrue in
        let asser = term_interp_and interp term in
        let conclu = disj_interp_app var notin f_name.why_name
          (List.map (fun (x,_) -> LVar x) params) in
        let asser = make_equiv asser conclu in
        let params = var::params in
        let asser = make_forall_list params [] asser in
        let asser = Goal(KAxiom,id_no_loc axiom_name,asser) in
        asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Goal(KAxiom,_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          define_disj notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv;assert false

  let rec add_triggers tr = function
    | LForall(vn,vt,[],(LForall _ as t)) -> LForall(vn,vt,[],add_triggers tr t)
    | LForall(vn,vt,trs,t) -> LForall(vn,vt,tr::trs,t)
    | _ -> assert false

  let rec define_frame_between notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai transformation
           d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,_,l)] ->
        let name = (in_name notin f_name.why_name) in
        Options.lprintf "Define logic in : %s :@." name;
        (* let acc = Logic(false, name, params, NotIn.ty notin)::acc in *)
        let var = ("jc_mem", notin.NotIn.ty_mem) in
        let gen_case acc (ident,assertion) =
          let effects = inductive_extract_effect assertion in
          let effects =
            List.filter (fun (s,_) -> not (s = select_name)) effects in
          let effects = List.filter (mem_are_compatible notin) effects in
          let nb = ref 0 in
          let rewrite acc (seff,lteff) =
            incr nb;
            let frameeff = frame_between_interp_app var notin seff lteff in
            let rw s lt =
              make_impl frameeff (frame_between_interp_app var notin s lt) in
            let assertion =
              LForall(fst var,snd var,[],
                      rewrite_inductive_case rw assertion) in
            let assertion = add_triggers [LPatP frameeff] assertion in
            (ident^(string_of_int !nb), assertion) :: acc in
          List.fold_left rewrite acc effects in
        let l = List.fold_left gen_case [] l in
        let constr acc (ident,assertion) =
          Goal(KAxiom,id_no_loc (frame_between_name^f_name.why_name^ident),
               assertion)::acc in
        List.fold_left constr acc l
      | [Function (_,f_name,params,_,term)] ->
          let name = in_name notin f_name.why_name in
          Options.lprintf "Generate logic notin (fun): %s :@." name;
          let acc = Logic(false,
                          {f_name with why_name = name},
                          params,
                          NotIn.ty notin)::acc in
          let axiom_name = "axiom"^"_in_"^(NotIn.mem_name2 notin)^f_name.why_name in
          Options.lprintf "Generate axiom notin : %s :@." axiom_name;
          let var = ("jc_mem",NotIn.ty notin) in
          let interp s lt =
            if mem_are_compatible notin (s,lt) && s <> select_name
            then frame_between_interp_app var notin s lt
            else LFalse in
          let asser = term_interp_or interp term in
          let conclu = frame_between_interp_app var notin f_name.why_name
            (List.map (fun (x,_) -> LVar x) params) in
          let asser = make_equiv asser conclu in
          let params = var::params in
          let asser = make_forall_list params [] asser in
          let asser = Goal(KAxiom,id_no_loc axiom_name,asser) in
          asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Goal(KAxiom,_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          define_frame_between notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv;assert false


  let rec define_sub notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai transformation
           d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,_,l)] ->
        let name = (in_name notin f_name.why_name) in
        let var = ("jc_var",NotIn.ty notin) in
        let gen_case acc (ident,assertion) =
          let effects = inductive_extract_effect assertion in
          let effects =
            List.filter (fun (s,_) -> not (s = select_name)) effects in
          let effects = List.filter (mem_are_compatible notin) effects in
          let rw seff lteff s lt =
            sub_interp_app (`App (seff,lteff)) notin (`App (s,lt)) in
          let nb = ref 0 in
          let rewrite acc (seff,lteff) =
            incr nb;
            let assertion =
              LForall(fst var,snd var,[],
                      rewrite_inductive_case (rw seff lteff) assertion) in
            (ident^(string_of_int !nb), assertion) :: acc in
          List.fold_left rewrite acc effects in
        let name = ("Sub"^name) in
        let l = List.fold_left gen_case [] l in
        let constr acc (ident,assertion) =
          Goal(KAxiom,id_no_loc (name^ident),assertion)::acc in
        let acc = List.fold_left constr acc l in
        acc
      | [Function (_,f_name,params,_,term)] ->
          let name = in_name notin f_name.why_name in
          Options.lprintf "Generate logic notin (fun): %s :@." name;
          let acc = Logic(false,
                          id_no_loc name,
                          params,
                          NotIn.ty notin)::acc in
          let axiom_name = "axiom"^"_in_"^(NotIn.mem_name2 notin)^f_name.why_name in
          Options.lprintf "Generate axiom notin : %s :@." axiom_name;
          let var = ("jc_var",NotIn.ty_elt notin) in
          let interp s lt =
            if mem_are_compatible notin (s,lt)
            then in_interp_app var notin s lt
            else LFalse in
          let asser = term_interp_or interp term in
          let conclu = in_interp_app var notin f_name.why_name
            (List.map (fun (x,_) -> LVar x) params) in
          let asser = make_equiv asser conclu in
          let params = var::params in
          let asser = make_forall_list params [] asser in
          let asser = Goal(KAxiom,id_no_loc axiom_name,asser) in
          asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Goal(KAxiom,_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          define_sub notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv;assert false

  let rec define_x_sub notin ta_conv acc =
    match ta_conv with
        (* Devrait peut-être utiliser la vrai transformation
           d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,_,l)] ->
        let name = (in_name notin f_name.why_name) in
        Options.lprintf "Define logic in : %s :@." name;
        (* let acc = Logic(false, name, params, NotIn.ty notin)::acc in *)
        let var = ("jc_var",NotIn.ty notin) in
        let gen_case acc (ident,assertion) =
          let effects = inductive_extract_effect assertion in
          let effects =
            List.filter (fun (s,_) -> not (s = select_name)) effects in
          let effects = List.filter (mem_are_compatible notin) effects in
          let rw seff lteff s lt =
            LImpl(sub_interp_app (`Var var) notin (`App (seff,lteff)),
                  sub_interp_app (`Var var) notin (`App (s,lt))) in
          let nb = ref 0 in
          let rewrite acc (seff,lteff) =
            incr nb;
            let assertion =
              LForall(fst var,snd var,[],
                      rewrite_inductive_case (rw seff lteff) assertion) in
            (ident^(string_of_int !nb), assertion) :: acc in
          List.fold_left rewrite acc effects in
        let name = ("X_Sub"^name) in
        let l = List.fold_left gen_case [] l in
        let constr acc (ident,assertion) =
          Goal(KAxiom,id_no_loc (name^ident),assertion)::acc in
        let acc = List.fold_left constr acc l in
        acc
      | [Function (_,f_name,params,_,term)] ->
          let name = in_name notin f_name.why_name in
          Options.lprintf "Generate logic notin (fun): %s :@." name;
          let acc = Logic(false,
                          {f_name with why_name = name},
                          params,
                          NotIn.ty notin)::acc in
          let axiom_name = "axiom"^"_in_"^(NotIn.mem_name2 notin)^f_name.why_name in
          Options.lprintf "Generate axiom notin : %s :@." axiom_name;
          let var = ("jc_var",NotIn.ty_elt notin) in
          let interp s lt =
            if mem_are_compatible notin (s,lt)
            then in_interp_app var notin s lt
            else LFalse in
          let asser = term_interp_or interp term in
          let conclu = in_interp_app var notin f_name.why_name
            (List.map (fun (x,_) -> LVar x) params) in
          let asser = make_equiv asser conclu in
          let params = var::params in
          let asser = make_forall_list params [] asser in
          let asser = Goal(KAxiom,id_no_loc axiom_name,asser) in
          asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Goal(KAxiom,_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          define_x_sub notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv;assert false

  let rec define_sub_x notin ta_conv acc =
    match ta_conv with
      (* Devrait peut-être utiliser la vrai transformation
         d'inductif en 1 unique axiom*)
      | [Inductive (_,f_name,_,l)] ->
        let name = (in_name notin f_name.why_name) in
        let var = ("jc_var",NotIn.ty notin) in
        let gen_case acc (ident,assertion) =
          let effects = inductive_extract_effect assertion in
          let effects = List.filter (mem_are_compatible notin) effects in
          let rw s lt =
            List.fold_left (fun acc (seff,lteff) ->
              LImpl(sub_interp_app (`App (seff,lteff)) notin (`Var var),acc))
              (sub_interp_app  (`App (s,lt)) notin (`Var var)) effects in
          let rewrite acc =
            let assertion =
              LForall(fst var,snd var,[],
                      rewrite_inductive_case rw assertion) in
            (ident, assertion) :: acc in
          rewrite acc in
        let name = ("Sub_X"^name) in
        let l = List.fold_left gen_case [] l in
        let constr acc (ident,assertion) =
          Goal(KAxiom,id_no_loc (name^ident),assertion)::acc in
        let acc = List.fold_left constr acc l in
        acc
      | [Function (_,f_name,params,_,term)] ->
        let axiom_name = "axiom"^"_disj_"^(NotIn.mem_name2 notin)^f_name.why_name in
        Options.lprintf "Generate axiom disj : %s :@." axiom_name;
        let var = ("jc_var",NotIn.ty notin) in
        let interp s lt =
          if mem_are_compatible notin (s,lt)
          then disj_interp_app var notin s lt
          else LTrue in
        let asser = term_interp_and interp term in
        let conclu = disj_interp_app var notin f_name.why_name
          (List.map (fun (x,_) -> LVar x) params) in
        let asser = make_equiv asser conclu in
        let params = var::params in
        let asser = make_forall_list params [] asser in
        let asser = Goal(KAxiom,id_no_loc axiom_name,asser) in
        asser::acc
      | [Logic(_bool,f_name,params,_ltype);
         Goal(KAxiom,_,ax_asser)] ->
          let rec extract_term = function
            | LForall (_,_,_,asser) -> extract_term asser
            | LPred("eq", [ _; b ]) -> b
            | _ -> assert false (* constructed by tr_fun_def *) in
          let term = extract_term ax_asser in
          let ta_conv = [Function (_bool,f_name,params,_ltype,term)] in
          define_sub_x notin ta_conv acc
      | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
          Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv;assert false

  let gen axiom_name f_name gen_framed in_update params framed_params =
    (* frame for one update *)
    let elt = "elt"^tmp_suffix in
    let elt_val = "elt_val"^tmp_suffix in
    let framed_normal_params = framed_params
      |> List.map fst in
    let framed_update_params =
      let notin_mem_name = NotIn.mem_name in_update in
      List.map (fun name ->
        if name = notin_mem_name then
          LApp("store",[LVar name;LVar elt;LVar elt_val])
        else LVar name
      ) framed_normal_params in
    let framed_normal_params = framed_normal_params
      |> List.map make_var in
    let params = params
      |> List.map fst
      |> List.map make_var in
    let sepa =
      LNot (MyBag.make_in (LVar elt)
              (LApp (in_name in_update f_name,params))) in
    let a,trig =
      match gen_framed with
        | `Pred gen_framed ->
            let pred_normal = gen_framed framed_normal_params in
            let pred_update = gen_framed framed_update_params in
            LImpl(pred_normal,pred_update),LPatP pred_update
        | `Term gen_framed ->
            let term_normal = gen_framed framed_normal_params in
            let term_update = gen_framed framed_update_params in
            make_eq term_normal term_update, LPatT term_update in
    let a = LImpl(sepa,a) in
    let a = make_forall_list framed_params [[trig]] a in
    let a = LForall (elt,NotIn.ty_elt in_update,[],
                     LForall (elt_val,NotIn.ty_elt_val in_update,[],a)) in
    let axiom_name = "axiom"^"_no_update_"^axiom_name^
      (NotIn.mem_name in_update) in
    Goal(KAxiom,id_no_loc axiom_name,a)

  let gen_many axiom_name f_name gen_framed notins params framed_params =
    (* frame for many update *)
    let mems = List.map (fun notin ->
      let mem_name = NotIn.mem_name notin in
      let ft = "ft"^mem_name^tmp_suffix in
      let mem1 = mem_name in
      let mem2 = mem_name^"2" in
      (ft,mem1,mem2,notin)) notins in
    let framed_normal_params = framed_params
      |> List.map fst in
    let rec assoc_default mem default = function
      | [] -> default
      | (_,mem1,mem2,_)::_ when mem = mem1 -> mem2
      | _::l -> assoc_default mem default l in
    let framed_update_params =
      List.map (fun name -> LVar (assoc_default name name mems))
        framed_normal_params in
    let framed_normal_params = framed_normal_params
      |> List.map make_var in
    let params = params
      |> List.map fst
      |> List.map make_var in
    let make_hyp (ft,mem1,mem2,notin) =
      let sepa1 = LPred(frame_between_name, [LVar ft;
                                             LVar mem2;
                                             LVar mem1]) in
      let sepa2 = LPred(disj_pred,[LVar ft;
                                   LApp(in_name notin f_name,params)]) in
      (sepa1,sepa2) in
    let hyps = List.map make_hyp mems in
    let impls = List.fold_left
      (fun acc (sepa1,sepa2) -> sepa1::sepa2::acc) [] hyps in
    let conclu,trig =
      match gen_framed with
        | `Pred gen_framed ->
            let pred_normal = gen_framed framed_normal_params in
            let pred_update = gen_framed framed_update_params in
            LImpl(pred_normal,pred_update),LPatP pred_update
        | `Term gen_framed ->
            let term_normal = gen_framed framed_normal_params in
            let term_update = gen_framed framed_update_params in
            make_eq term_normal term_update, LPatT term_update in
    let a = make_impl_list conclu impls  in
    let trigs = List.fold_left
      (fun acc (sepa1,_) -> (LPatP sepa1)::acc) [trig] hyps in
    let a = make_forall_list framed_params [trigs] a in
    let make_foralls acc (ft,_,mem2,notin) =
      (ft,NotIn.ty notin)::(mem2,notin.NotIn.ty_mem)::acc in
    let foralls = List.fold_left make_foralls [] mems in
    let a = make_forall_list foralls [] a in
    let axiom_name = "axiom"^"_no_frame_"^axiom_name^
      (String.concat "_"
         (List.map (fun (_,_,_,notin) -> NotIn.mem_name notin) mems))
    in
    Goal(KAxiom,id_no_loc axiom_name,a)



  let def_frame_in f_name notin params acc notin_updates =
    let in_name = in_name notin f_name in
    let gen_framed = `Term (fun params -> LApp(in_name,params)) in
    let acc = List.fold_left
        (fun acc notin_update ->
         (gen in_name f_name gen_framed notin_update params params) ::acc)
        acc notin_updates in
    let acc = List.fold_all_part
      (fun acc part -> match part with | [] -> acc (* trivial axiom *)
        | notin_updates ->
          gen_many in_name f_name gen_framed notin_updates params params ::acc)
      acc notin_updates in
    acc

  (** framed_name must have the same param than f_name *)
  let def_frame framed_name is_pred f_name params acc notin_updates =
    let gen_framed =
      if is_pred
      then `Pred (fun params -> LPred(framed_name,params))
      else `Term (fun params -> LApp(framed_name,params)) in
    let acc = List.fold_left
      (fun acc notin_update ->
        (gen framed_name f_name gen_framed notin_update params params)::acc)
      acc notin_updates in
    let acc = List.fold_all_part
      (fun acc part -> match part with | [] -> acc (* trivial axiom *)
        | notin_updates ->
          gen_many framed_name f_name gen_framed notin_updates params params ::acc)
      acc notin_updates in
    acc

  let in_for_in f_name args notin framed acc =
    let name = in_name notin f_name in
    let acc = Logic(false, id_no_loc name, args, NotIn.ty notin)::acc in
    let var = ("jc_var",NotIn.ty_elt notin) in
    let conjs = List.map
      (fun (f,params) ->
         (in_interp_app var notin f.li_name
            (List.map (fun (x,_) -> LVar x) params)))
      framed in
    let code = make_and_list conjs in
    let conclu = in_interp_app var notin f_name
      (List.map (fun (x,_) -> LVar x) args) in
    let code = make_equiv code conclu in
    let code = make_forall_list (var::args) [] code in
    let axiom_name = name^"_def" in
    Goal(KAxiom,id_no_loc axiom_name,code)::acc

  let disj_for_in f_name args notin framed acc =
    let name = in_name notin f_name in
    let var = ("jc_var",NotIn.ty notin) in
    let conjs = List.map
      (fun (f,params) ->
         (disj_interp_app var notin f.li_name
            (List.map (fun (x,_) -> LVar x) params)))
      framed in
    let code = make_and_list conjs in
    let conclu = disj_interp_app var notin f_name
      (List.map (fun (x,_) -> LVar x) args) in
    let code = make_equiv code conclu in
    let code = make_forall_list (var::args) [] code in
    let axiom_name = name^"_disj_def" in
    Goal(KAxiom,id_no_loc axiom_name,code)::acc

  let x_sub_for_in f_name args notin framed acc =
    let name = in_name notin f_name in
    let var = ("jc_var",NotIn.ty notin) in
    let conjs = List.map
      (fun (f,params) ->
         (sub_interp_app (`Var var) notin (`App (f.li_name,
            (List.map (fun (x,_) -> LVar x) params)))))
      framed in
    let code = make_and_list conjs in
    let conclu = sub_interp_app (`Var var) notin (`App (f_name,
      (List.map (fun (x,_) -> LVar x) args))) in
    let code = make_equiv code conclu in
    let code = make_forall_list (var::args) [] code in
    let axiom_name = name^"_x_sub_def" in
    Goal(KAxiom,id_no_loc axiom_name,code)::acc

  let sub_x_for_in f_name args notin framed acc =
    let name = in_name notin f_name in
    let var = ("jc_var",NotIn.ty notin) in
    let conjs = List.map
      (fun (f,params) ->
         (sub_interp_app  (`App (f.li_name,
            (List.map (fun (x,_) -> LVar x) params)))) notin (`Var var))
      framed in
    let code = make_and_list conjs in
    let conclu = sub_interp_app (`App (f_name,
      (List.map (fun (x,_) -> LVar x) args))) notin (`Var var) in
    let code = make_equiv code conclu in
    let code = make_forall_list (var::args) [] code in
    let axiom_name = name^"_sub_x_def" in
    Goal(KAxiom,id_no_loc axiom_name,code)::acc


end

let lemma_disjoint_cases ta_conv acc =
  match ta_conv with
    | [Inductive (_,f_name,params,l)] ->
      let rec link_by_implication args cases = function
        | LForall (s,ty,_,f) ->
          LForall(s,ty,[],link_by_implication args cases f)
        | LImpl(f1,f2) -> LImpl(f1,link_by_implication args cases f2)
        | LPred(s,lt) when f_name.why_name = s ->
          let equalities = List.map2 (fun (a1,_) a2 -> make_eq (LVar a1) a2)
            args lt in
          LImpl (make_and_list equalities,each_case args cases)
        | _ -> failwith "Inductive must be forall x,.. Pn -> ... -> P1"
      and each_case args = function
        | [] -> LFalse
        | (_,assertion)::cases -> link_by_implication args cases assertion in
      let args = List.map (fun (s,ty) -> (s^tmp_suffix,ty)) params in
      let condition = make_forall_list args [] (each_case args l) in
      let goal_name = f_name.why_name^"_disjoint_case" in
      Goal(KGoal,id_no_loc goal_name,condition)::acc
    | _ -> Options.lprintf "@[<hov 3>I can't translate that :@\n%a"
      Why_pp.(print_list newline Output.fprintf_why_decl) ta_conv;assert false






let tr_logic_fun_aux f ta acc =

  if Options.debug then
    Format.printf "[interp] logic function %s@." f.li_final_name;

  let lab =
    match f.li_labels with [lab] -> lab | _ -> LabelHere
  in

  let fa =
    assertion ~type_safe:false ~global_assertion:true ~relocate:false lab lab
  in
  let ft =
    term ~type_safe:false ~global_assertion:true ~relocate:false lab lab
  in
  let term_coerce = term_coerce ~type_safe:false ~global_assertion:true lab in

  let params = tr_params_usual_model f in
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
    if Options.gen_frame_rule_with_ft
    then
      let acc = if Hashtbl.mem pragma_gen_sep f.li_tag
      then begin
        (* use_predicate *)
        let (_,which) = Hashtbl.find pragma_gen_sep f.li_tag in
        let todos =
          Hashtbl.find_all predicates_to_generate f.li_tag in
        let fold acc = function
          | `Logic (f,_,params) -> (f,make_args ~parameters:params f) ::acc
          | `Pointer _ -> acc in
        let framed = List.fold_left fold [] which in
        let args = make_args f in
        let print_todo fmt = function
          | (`In,_) -> fprintf fmt "in"
          | (`Disj,_) -> fprintf fmt "disj" in
        Options.lprintf "user predicate %s asks to generate : %a@."
          f.li_name Why_pp.(print_list comma print_todo) todos;
        let make_todo acc (todo,notin) =
          match todo with
            | `In ->
              let fname = f.li_name in
              let acc =
                InDisj.in_for_in fname args notin framed acc in
              let acc =
                InDisj.x_sub_for_in fname args notin framed acc in
              let acc =
                InDisj.sub_x_for_in fname args notin framed acc in
              acc
            | `Disj ->
              InDisj.disj_for_in f.li_name args notin framed acc in
        let acc = List.fold_left make_todo acc todos in
        acc
      end
      else begin
        let f_name = f.li_final_name in
        let todos =
          Hashtbl.find_all predicates_to_generate f.li_tag in
        let filter_notin acc = function
          | (`In , notin) -> notin::acc
          | _ -> acc in
        (* notin_updates is used to create the frames axioms *)
        let notin_updates = List.fold_left filter_notin [] todos in
        let print_todo fmt = function
           | (`Disj,_) -> fprintf fmt "disj"
           | (`In,_) -> fprintf fmt "in" in
        Options.lprintf "%s asks to generate : %a@."
          f_name Why_pp.(print_list comma print_todo) todos;
        let acc = if todos = [] then acc else
            lemma_disjoint_cases fun_def acc in
        let make_todo acc (todo,notin) =
          match todo with
            | `In ->
                let acc = InDisj.define_In notin fun_def acc in
                let acc = InDisj.define_frame_between notin fun_def acc in
                let acc = InDisj.define_sub notin fun_def acc in
                let acc = InDisj.define_x_sub notin fun_def acc in
                let acc = InDisj.define_sub_x notin fun_def acc in
                let acc = InDisj.define_sub notin fun_def acc in
                let acc =
                  InDisj.def_frame_in f_name notin params acc notin_updates in
                acc
            | `Disj ->
                let acc = InDisj.define_disj notin fun_def acc  in
                acc in
        let acc = List.fold_left make_todo acc todos in
        let is_pred = f.li_result_type = None in
        InDisj.def_frame f_name is_pred f_name params acc notin_updates
      end in
      if Hashtbl.mem Typing.pragma_gen_same f.li_tag then
        let f_name = f.li_final_name in
        let mirror =
          Hashtbl.find Typing.pragma_gen_same f.li_tag in
        let mirror_name = mirror.li_final_name in
        let todos =
          Hashtbl.find_all predicates_to_generate mirror.li_tag in
        let filter_notin acc = function
          | (`In , notin) -> notin::acc
          | _ -> acc in
        (* notin_updates is used to create the frames axioms *)
        let notin_updates = List.fold_left filter_notin [] todos in
        Options.lprintf "Frame of %s using footprint of %s@."
          f_name mirror_name;
        let is_pred = f.li_result_type = None in
        InDisj.def_frame f_name is_pred mirror_name params acc notin_updates
      else acc
    else acc in
  acc


(*   (\* full_separated axioms. *\) *)
(*   let sep_preds =  *)
(*     List.fold_left (fun acc vi -> *)
(*       match vi.vi_type with *)
(*         | JCTpointer(st,_,_) ->  *)
(*             LPred("full_separated",[LVar "tmp";
               LVar vi.vi_final_name]) *)
(*             :: acc *)
(*         | _ -> acc *)
(*     ) [] li.li_parameters *)
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
(*         match li.li_result_type with *)
(*           | None -> *)
(*               LImpl( *)
(*                 make_and_list sep_preds, *)
(*                 LIff( *)
(*                   LPred(li.li_final_name,normal_params), *)
(*                   LPred(li.li_final_name,update_params))) *)
(*           | Some rety -> *)
(*               LImpl( *)
(*                 make_and_list sep_preds, *)
(*                 LPred("eq",[ *)
(*                   LApp(li.li_final_name,normal_params); *)
(*                   LApp(li.li_final_name,update_params)])) *)
(*       in *)
(*       let a =  *)
(*         List.fold_left (fun a (name,ty) -> LForall(name,ty,a))
           a params_reads *)
(*       in *)
(*       let structty = match mc with  *)
(*         | FVfield fi -> JCtag(fi.fi_struct, []) *)
(*         | FVvariant vi -> JCvariant vi *)
(*       in *)
(*       let basety = match mc with *)
(*         | FVfield fi -> tr_base_type fi.fi_type *)
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
(*         | FVfield fi -> fi.fi_name *)
(*         | FVvariant vi -> vi.ri_name *)
(*       in *)
(*       Axiom( *)
(*         "full_separated_" ^ li.li_name ^ "_" ^ mcname, *)
(*         a) :: acc *)
(*     ) li.li_effects.e_memories acc *)


let tr_logic_fun ft ta acc = tr_logic_fun_aux ft ta acc

(*
  Local Variables:
  compile-command: "unset LANG; make -C .. bin/jessie.byte"
  End:
*)
