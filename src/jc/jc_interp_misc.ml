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
open Struct_tools

open Output_ast
open Why_pp
open Format

module O = Output

let find_struct a = fst @@ StringHashtblIter.find Typing.structs_table a

let find_variant a = StringHashtblIter.find Typing.roots_table a

let find_pointer_class a =
  try
    JCtag (find_struct a, []) (* TODO: fill parameters ? *)
  with Not_found ->
    JCroot (find_variant a)

let mutable_name2 a =
  mutable_name (JCtag (find_struct a, []))

let committed_name2 a =
  committed_name (JCtag (find_struct a, []))

let pc_of_name name = JCtag (find_struct name, []) (* TODO: parameters *)

let const t c =
  match c with
  | JCCvoid -> O.(const (ty t) Void)
  | JCCnull -> invalid_arg "const"
  | JCCreal s -> O.(const (ty t) (Real s))
  | JCCinteger s -> O.(const (ty t) (Int s))
  | JCCboolean b -> O.(const (ty t) (Bool b))
  | JCCstring _s ->
    Options.jc_error Why_loc.dummy_position "Unsupported string constant" (* TODO *)

(******************************************************************************)
(*                              environment                                   *)
(******************************************************************************)

let current_behavior : string option ref = ref None
let set_current_behavior behav = current_behavior := Some behav
let reset_current_behavior () = current_behavior := None
let get_current_behavior () =
  match !current_behavior with None -> assert false | Some behav -> behav
let safety_checking () = get_current_behavior () = "safety"
let variant_checking () =
  let behv = get_current_behavior () in
  behv = "safety" || behv = "variant"

let is_current_behavior id = id = get_current_behavior ()

let in_behavior b lb =
  match lb with
  | [] -> b = "default"
  | _ -> List.exists (fun behav -> behav#name = b) lb

let in_current_behavior b = in_behavior (get_current_behavior ()) b

let in_default_behavior b = in_behavior "default" b


let current_spec : fun_spec option ref = ref None
let set_current_spec s = current_spec := Some s
let reset_current_spec () = current_spec := None
let get_current_spec () =
  match !current_spec with None -> assert false | Some s -> s

let make_label_counter prefix =
  let c = ref 0 in
  fun () ->
    incr c;
    let name = prefix ^ string_of_int !c in
    { lab_name = name;
      lab_final_name = name;
      lab_times_used = 1 }

let fresh_loop_label = make_label_counter "loop_"
let fresh_reinterpret_label = make_label_counter "l__before_reinterpret_"
let fresh_statement_label = make_label_counter "l__before_statement_"

(******************************************************************************)
(*                                   types                                    *)
(******************************************************************************)

(* basic model types *)

let root_model_type ri = O.(lt ~from:(Name.Theory.root ri) (Name.Type.root ri) @@@$ Nil)

let struct_model_type st = root_model_type (struct_root st)

let pointer_class_model_type pc = root_model_type (pointer_class_root pc)

let bitvector_type = O.(lt ~from:(Name.Theory.bitvector) Name.Type.bitvector @@@$ Nil)

let alloc_class_type =
  function
  | JCalloc_root vi -> root_model_type vi
  | JCalloc_bitvector -> O.void_lt

let memory_class_type mc = alloc_class_type (alloc_class_of_mem_class mc)

(* raw types *)

let raw_pointer_type ty' = O.(jc_lt pointer_type_name @@@$. ty')

let raw_pset_type ty' = O.(jc_lt pset_type_name @@@$. ty')

let raw_alloc_table_type ty' = O.(jc_lt Name.Type.alloc_table @@@$. ty')

let raw_tag_table_type ty' = O.(jc_lt Name.Type.tag_table @@@$. ty')

let raw_tag_id_type ty' = O.(jc_lt tag_id_type_name @@@$. ty')

let raw_memory_type ty1' ty2' = O.(jc_lt Name.Type.memory @@@$ ty1' @@@. ty2')

(* pointer model types *)

let pointer_type ac pc =
  match ac with
  | JCalloc_root _ ->
    raw_pointer_type (pointer_class_model_type pc)
  | JCalloc_bitvector ->
    raw_pointer_type O.void_lt

(* translation *)

let tr_native_type t =
  function
  | Tunit -> O.(logic_type (ty t) void_lt)
  | Tboolean -> O.(logic_type (ty t) bool_lt)
  | Tinteger -> O.(logic_type (ty t) integer_lt)
  | Treal -> O.(logic_type (ty t) real_lt)
  | Tgenfloat `Double -> O.(logic_type (ty t) double_lt)
  | Tgenfloat `Float -> O.(logic_type (ty t) single_lt)
  | Tgenfloat `Binary80 -> O.(logic_type t (jc_lt "binary80" @@@$ Nil))
  | Tstring -> O.(logic_type t (jc_lt "string" @@@$ Nil))

type any_ltype_hlist =
  | Ltype_hlist : 'a ltype_hlist -> any_ltype_hlist

let rec tr_base_type : type a b. (a, b) O.ty_opt -> ?region:_ ->  _ -> a logic_type =
  fun t ?region ->
  let tr_ltype_hlist =
    List.fold_left
      (fun (Ltype_hlist lhl) t -> Ltype_hlist O.(tr_base_type Any ?region t @@@ lhl))
      (Ltype_hlist Nil)
  in
  function
  | JCTnative ty -> tr_native_type t ty
  | JCTlogic (s, l) ->
    O.(logic_type t (let Ltype_hlist lhl = tr_ltype_hlist l in lt ~from:Name.Theory.current s @@@$ lhl))
  | JCTenum ei ->
    begin match ei.ei_type, t with
      | Int (r, b), _ -> O.(logic_type (ty t) (int_lt (Int (r, b))))
      | Enum s, O.Enum s' when s = s' -> O.(logic_type (Enum s) (enum_lt s))
      | Enum s, O.Enum s' -> failwith ("tr_base_type: enum type mismatch: expected `" ^ s ^ "', got " ^ s')
      | Enum s, O.Any -> failwith ("tr_base_type: enum type mismatch: expected `" ^ s ^ "', got \"some type\"")
      | Enum s, O.Ty t -> failwith ("tr_base_type: type mismatch: expected enum `" ^ s ^ "', got " ^ O.string_of_ty t)
    end
  | JCTpointer (pc, _, _) ->
    let ac =
      match region with
      | None ->
        alloc_class_of_pointer_class pc
      | Some r when Region.bitwise r -> JCalloc_bitvector
      | Some _ -> alloc_class_of_pointer_class pc
    in
    O.(logic_type Any (pointer_type ac pc))
  | JCTnull | JCTany -> invalid_arg "tr_base_type"
  | JCTtype_var tv -> O.(logic_type t (var_lt (Type_var.uname tv)))

let tr_type t ~region ty = Base_type (tr_base_type t ~region ty)

let tr_var_base_type t v = tr_base_type t ~region:v.vi_region v.vi_type

let tr_var_type t v = tr_type t ~region:v.vi_region v.vi_type

let any_value t region jct =
  match jct with
  | JCTnative ty ->
    begin match ty with
    | Tunit -> O.void_e
    | Tboolean -> make_app "any_bool" [void]
    | Tinteger -> make_app "any_int" [void]
    | Treal -> make_app "any_real" [void]
    | Tgenfloat _ -> make_app ("any_" ^ native_name ty) [void]
    | Tstring -> make_app "any_string" [void]
    end
  | JCTnull
  | JCTpointer _ -> make_app ~ty:(tr_type ~region t) "any_pointer" [void]
  | JCTenum ri -> make_app (fun_any_enum_name ri) [void]
  | JCTlogic _ as ty ->
    let t =
      Annot_type(LTrue, Base_type (tr_base_type ty), [], [], LTrue, [])
    in mk_expr (BlackBox t)
  | JCTany -> failwith "any_value: value of wilcard type"
  | JCTtype_var _ ->
    Options.jc_error Why_loc.dummy_position "Usnupported value of poly type" (* TODO: need environment *)

(* model types *)

let pset_type ac = raw_pset_type (alloc_class_type ac)

let alloc_table_type ac = raw_alloc_table_type (alloc_class_type ac)

let tag_table_type vi = raw_tag_table_type (root_model_type vi)

let tag_id_type vi = raw_tag_id_type (root_model_type vi)

let memory_type mc =
  let value_type =
    match mc with
    | JCmem_field fi -> tr_base_type fi.fi_type
    | JCmem_plain_union _
    | JCmem_bitvector -> bitvector_type
  in
  raw_memory_type (memory_class_type mc) value_type

(* query model types *)

let is_alloc_table_type ty' = ty'.lt_name = Name.Type.alloc_table

let is_tag_table_type ty' = ty'.lt_name = Name.Type.tag_table

let is_memory_type ty' = ty'.lt_name = Name.Type.memory

let deconstruct_memory_type_args ty =
  match ty.lt_args with [t; v] -> t, v | _ -> invalid_arg "deconstruct_memory_type_args"


(******************************************************************************)
(*                                 variables                                  *)
(******************************************************************************)

let transpose_label ~label_assoc lab =
  match label_assoc with
  | None -> lab
  | Some l ->  try List.assoc lab l with Not_found -> lab

let lvar_name ~label_in_name ?label_assoc lab n =
  let lab = transpose_label ~label_assoc lab in
  if label_in_name then
    match lab with
    | LabelHere -> n
    | LabelOld -> invalid_arg "lvar_name"
    | LabelPre -> n ^ "_at_Pre"
    | LabelPost -> n ^ "_at_Post"
    | LabelName lab -> n ^ "_at_" ^ lab.lab_final_name
  else n

let lvar ~constant ~label_in_name lab n =
  let n = lvar_name ~label_in_name lab n in
  if constant then
    LVar n
  else if label_in_name then
    LDeref n
  else
    match lab with
    | LabelHere -> LDeref n
    | LabelOld -> LDerefAtLabel (n, "")
    | LabelPre -> LDerefAtLabel (n, "init")
    | LabelPost -> LDeref n
    | LabelName lab -> LDerefAtLabel (n, lab.lab_final_name)

(* simple variables *)

let plain_var n = mk_var n
let deref_var n = mk_expr (Deref n)

let var_name' e =
  match e.expr_node with
  | Var n | Deref n -> n
  | _ -> invalid_arg "var_name'"

let var v =
  if v.vi_assigned
  then deref_var v.vi_final_name
  else plain_var v.vi_final_name

let param ~type_safe v =
  v.vi_final_name,
  if type_safe then
    tr_base_type v.vi_type
  else
    tr_base_type ~region:v.vi_region v.vi_type

let tvar_name ~label_in_name lab v =
  let constant = not v.vi_assigned in
  lvar_name ~label_in_name:(label_in_name && not constant)
    lab v.vi_final_name

let tvar ~label_in_name lab v =
  let constant = not v.vi_assigned in
  lvar ~constant ~label_in_name:(label_in_name && not constant)
    lab v.vi_final_name

let tparam ~label_in_name lab v =
  tvar_name ~label_in_name lab v,
  tvar ~label_in_name lab v,
  tr_base_type v.vi_type

let local_of_parameter (v', ty') = (var_name' v',ty')
let effect_of_parameter (v', _ty') = var_name' v'
let wparam_of_parameter (v', ty') = (v',Ref_type(Base_type ty'))
let rparam_of_parameter (v', ty') = (v',Base_type ty')

(* model variables *)

let mutable_memory infunction (mc, r) =
  if Region.polymorphic r then
    if Region.bitwise r then
      MemoryMap.exists (fun (_mc', r') _labs -> Region.equal r r')
        infunction.fun_effects.fe_writes.e_memories
    else
      MemoryMap.mem (mc, r)
        infunction.fun_effects.fe_writes.e_memories
  else true

let mutable_alloc_table infunction (ac, r) =
  if Region.polymorphic r then
    if Region.bitwise r then
      AllocMap.exists (fun (_ac', r') _labs -> Region.equal r r')
        infunction.fun_effects.fe_writes.e_alloc_tables
    else
      AllocMap.mem (ac, r)
        infunction.fun_effects.fe_writes.e_alloc_tables
  else true

let mutable_tag_table infunction (vi, r) =
  if Region.polymorphic r then
    if Region.bitwise r then
      TagMap.exists (fun (_vi',r') _labs -> Region.equal r r')
        infunction.fun_effects.fe_writes.e_tag_tables
    else
      TagMap.mem (vi, r)
        infunction.fun_effects.fe_writes.e_tag_tables
  else true

let plain_memory_var (mc, r) = mk_var @@ memory_name (mc, r)
let deref_memory_var (mc, r) = mk_expr @@ Deref (memory_name (mc, r))

let memory_var ?(test_current_function=false) (mc, r) =
  if test_current_function && !current_function = None then
    plain_memory_var (mc, r)
  else if mutable_memory (get_current_function ()) (mc,r ) then
    deref_memory_var (mc, r)
  else plain_memory_var (mc, r)

let tmemory_var ~label_in_name lab (mc,r) =
  let mem = memory_name (mc,r) in
  let constant =
    match !current_function with
    | None -> true
    | Some infunction -> not (mutable_memory infunction (mc,r))
  in
  lvar ~constant ~label_in_name lab mem

let plain_alloc_table_var (ac, r) = mk_var @@ Name.alloc_table (ac, r)
let deref_alloc_table_var (ac, r) = mk_expr @@ Deref (Name.alloc_table (ac, r))

let alloc_table_var ?(test_current_function=false) (ac, r) =
  if test_current_function && !current_function = None then
    plain_alloc_table_var (ac, r)
  else if mutable_alloc_table (get_current_function ()) (ac, r) then
    deref_alloc_table_var (ac, r)
  else plain_alloc_table_var (ac, r)

let talloc_table_var ~label_in_name lab (ac, r) =
  let alloc = Name.alloc_table (ac, r) in
  let constant =
    match !current_function with
    | None -> true
    | Some infunction -> not (mutable_alloc_table infunction (ac, r))
  in
  not constant, lvar ~constant ~label_in_name lab alloc


let plain_tag_table_var (vi, r) = mk_var @@ Name.tag_table (vi, r)
let deref_tag_table_var (vi, r) = mk_expr @@ Deref (Name.tag_table (vi, r))

let tag_table_var (vi, r) =
  if mutable_tag_table (get_current_function ()) (vi, r) then
    deref_tag_table_var (vi, r)
  else plain_tag_table_var (vi, r)

let ttag_table_var ~label_in_name lab (vi,r) =
  let tag = Name.tag_table (vi, r) in
  let constant =
    match !current_function with
    | None -> true
    | Some infunction -> not (mutable_tag_table infunction (vi,r))
  in
  not constant, lvar ~constant ~label_in_name lab tag

(******************************************************************************)
(*                           locations and separation                         *)
(******************************************************************************)

let ref_term : (?subst:(term Envset.VarMap.t) ->
                 type_safe:bool -> global_assertion:bool -> relocate:bool
                 -> label -> label -> Fenv.term -> term) ref
    = ref (fun ?(subst=VarMap.empty) ~type_safe:_ ~global_assertion:_
             ~relocate:_ _ _ _ ->
               assert (VarMap.is_empty subst);
               assert false)

let rec location ~type_safe ~global_assertion lab loc =
  let flocs = location_set ~type_safe ~global_assertion lab in
  let ft = !ref_term ~type_safe ~global_assertion ~relocate:false lab lab in
  match loc#node with
  | JCLvar _v ->
    LVar "pset_empty"
  | JCLderef (locs, _lab, _fi, _r) ->
    flocs locs
  | JCLderef_term (t1,_fi) ->
    LApp ("pset_singleton", [ft t1])
  | _ -> Options.jc_error loc#pos "Unsupported location" (* TODO *)

and location_set ~type_safe ~global_assertion lab locs =
  let flocs = location_set ~type_safe ~global_assertion lab in
  let ft = !ref_term ~type_safe ~global_assertion ~relocate:false lab lab in
  match locs#node with
  | JCLSvar v ->
    LApp ("pset_singleton", [tvar ~label_in_name:global_assertion lab v])
  | JCLSderef(locs,lab,fi,_r) ->
    let mc, _fi_opt = lderef_mem_class ~type_safe locs fi in
    let mem = tmemory_var ~label_in_name:global_assertion lab (mc, locs#region) in
    LApp ("pset_deref", [mem; flocs locs])
  | JCLSrange (locs, Some t1, Some t2) ->
    LApp ("pset_range", [flocs locs; ft t1; ft t2])
  | JCLSrange (locs, None, Some t2) ->
    LApp ("pset_range_left", [flocs locs; ft t2])
  | JCLSrange (locs, Some t1, None) ->
    LApp ("pset_range_right", [flocs locs; ft t1])
  | JCLSrange (locs, None, None) ->
    LApp ("pset_all", [flocs locs])
  | JCLSrange_term (locs, Some t1, Some t2) ->
    LApp ("pset_range", [LApp ("pset_singleton", [ft locs]); ft t1; ft t2])
  | JCLSrange_term (locs, None, Some t2) ->
    LApp ("pset_range_left", [LApp ("pset_singleton", [ft locs]); ft t2])
  | JCLSrange_term (locs, Some t1, None) ->
    LApp ("pset_range_right", [LApp("pset_singleton", [ft locs]); ft t1])
  | JCLSrange_term (locs, None, None) ->
    LApp ("pset_all", [LApp ("pset_singleton", [ft locs])])
  | JCLSat (locs, _lab) -> flocs locs

let rec pset_union_of_list =
  function
  | [] -> LVar "pset_empty"
  | [e'] -> e'
  | e' :: el' -> LApp ("pset_union", [e'; pset_union_of_list el'])

let separation_condition loclist1 loclist2 =
  let floc = location ~type_safe:false ~global_assertion:false LabelHere in
  let pset1, pset2 = Pair.map (pset_union_of_list % List.map floc) (loclist1, loclist2) in
  LPred ("pset_disjoint", [pset1; pset2])

type memory_effect = RawMemory of Memory.t | PreciseMemory of Location.t

exception No_region

let rec transpose_location ~region_assoc ~param_assoc (loc, (mc, rdist)) =
  match transpose_region ~region_assoc rdist with
  | None -> None
  | Some rloc ->
    try
      let rec mk_node loc =
        match loc#node with
        | JCLvar ({ vi_static = true } as v)  -> JCLvar v
        | JCLvar v ->
          begin match List.mem_assoc_eq VarOrd.equal v param_assoc with
          | None -> raise No_region (* Local variable *)
          | Some e ->
            match location_of_expr e with
            | None -> raise No_region
            | Some loc' -> loc'#node
          end
        | JCLderef (locs, lab, fi, r) ->
          let locs = transpose_location_set ~region_assoc ~param_assoc locs in
          JCLderef (locs, lab, fi, r) (* TODO: remove useless lab & r *)
        | JCLat (loc, lab) ->
          let node = mk_node loc in
          JCLat (new location_with ~typ:loc#typ ~region:rloc ~node loc, lab)
        | _ -> Options.jc_error loc#pos "Unsupported location" (* TODO *)
      in
      let node = mk_node loc in
      let loc = new location_with ~typ:loc#typ ~region:rloc ~node loc in
      Some (PreciseMemory (loc, (mc, rloc)))
    with
    | No_region -> Some (RawMemory (mc, rloc))

and transpose_location_set ~region_assoc ~param_assoc locs =
  match transpose_region ~region_assoc locs#region with
  | None -> raise No_region
  | Some rloc ->
    let node =
      match locs#node with
      | JCLSvar ({ vi_static = true } as v) -> JCLSvar v
      | JCLSvar v ->
        begin match List.mem_assoc_eq VarOrd.equal v param_assoc with
        | None -> raise No_region (* Local variable *)
        | Some e ->
          match location_set_of_expr e with
          | None -> raise No_region
          | Some locs' -> locs'#node
        end
      | JCLSderef (locs', lab, fi, r) ->
        let locs' = transpose_location_set ~region_assoc ~param_assoc locs' in
        JCLSderef(locs',lab,fi,r) (* TODO: remove useless lab & r *)
      | JCLSat (locs', lab) ->
        let locs' = transpose_location_set ~region_assoc ~param_assoc locs' in
        JCLSat (locs', lab)
      | _ -> Options.jc_error locs#pos "Unsupported location set" (* TODO *)
    in
    new location_set_with ~typ:locs#typ  ~region:rloc ~node locs

let transpose_location_set ~region_assoc ~param_assoc locs _w =
  try Some (transpose_location_set ~region_assoc ~param_assoc locs)
  with No_region -> None

let transpose_location_list ~region_assoc ~param_assoc rw_raw_mems rw_precise_mems (mc, distr) =
  if MemorySet.mem (mc, distr) rw_raw_mems then []
  else
    LocationSet.fold
      (fun (_, (_, r) as x) acc ->
         if Region.equal r distr then
           match transpose_location ~region_assoc ~param_assoc x with
           | None -> acc
           | Some (RawMemory _) -> failwith "transpose_location_list: got unexpected raw memory"
           | Some (PreciseMemory (loc, (_mc, _rloc))) -> loc :: acc
         else acc)
      rw_precise_mems
      []

let write_read_separation_condition
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc
    inter_names writes reads =
  ListLabels.fold_left reads
    ~init:LTrue
    ~f:(fun acc ((mc, distr), (v, _ty')) ->
       let n = var_name' v in
       if StringSet.mem n inter_names then
         (* There is a read/write interference on this memory *)
         ListLabels.fold_left writes
           ~init:acc
           ~f:(fun acc ((mc', distr'), (v', _ty')) ->
               let n' = var_name' v' in
               if n = n' then
                 let rw_raw_mems =
                   MemorySet.of_list
                     MemoryMap.(keys callee_reads.e_raw_memories
                                @ keys callee_writes.e_raw_memories)
                 in
                 let rw_precise_mems =
                   LocationSet.of_list
                     LocationMap.(keys callee_reads.e_precise_memories
                                  @ keys callee_writes.e_precise_memories)
                 in
                 let loclist =
                   transpose_location_list ~region_assoc ~param_assoc
                     rw_raw_mems rw_precise_mems (mc, distr)
                 in
                 let loclist' =
                   transpose_location_list ~region_assoc ~param_assoc
                     rw_raw_mems rw_precise_mems (mc', distr')
                 in
                 if loclist <> [] && loclist' <> [] then
                   let pre = separation_condition loclist loclist' in
                   make_and pre acc
                 else acc
               else acc)
       else acc)

let write_write_separation_condition
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc
    ww_inter_names writes _reads =
  let writes = List.filter (fun ((_mc,_distr), (v, _ty)) -> StringSet.mem (var_name' v) ww_inter_names) writes in
  let write_pairs = List.all_pairs writes in
  ListLabels.fold_left write_pairs
    ~init:LTrue
    ~f:(fun acc (((mc, distr), (v, _ty)), ((mc', distr'),(v', _ty'))) ->
        let n = var_name' v in
        let n' = var_name' v' in
        if n = n' then
          (* There is a write/write interference on this memory *)
          let rw_raw_mems =
            MemorySet.of_list
              MemoryMap.(keys callee_reads.e_raw_memories
                         @ keys callee_writes.e_raw_memories)
          in
          let rw_precise_mems =
            LocationSet.of_list
              LocationMap.(keys callee_reads.e_precise_memories
                           @ keys callee_writes.e_precise_memories)
          in
          let loclist =
            transpose_location_list ~region_assoc ~param_assoc
              rw_raw_mems rw_precise_mems (mc, distr)
          in
          let loclist' =
            transpose_location_list ~region_assoc ~param_assoc
              rw_raw_mems rw_precise_mems (mc',distr')
          in
          if loclist <> [] && loclist' <> [] then
            let pre = separation_condition loclist loclist' in
            make_and pre acc
          else acc
        else acc)

(******************************************************************************)
(*                                  effects                                   *)
(******************************************************************************)

let rec all_possible_memory_effects acc r (* ty *) =
  function
  | JCTpointer (pc, _, _) ->
    begin match pc with
    | JCroot _ -> acc (* TODO *)
    | JCtag (st, _) ->
      List.fold_left
        (fun acc fi ->
           let mc = JCmem_field fi in
           let mem = mc, r in
           if MemorySet.mem mem acc
           then acc
           else all_possible_memory_effects (MemorySet.add mem acc) r fi.fi_type)
        acc
        st.si_fields
    end
  | JCTnative _
  | JCTnull
  | JCTenum _
  | JCTlogic _
  | JCTany -> acc
  | JCTtype_var _ ->
    Options.jc_error Why_loc.dummy_position "Unsupported effect for poly expression" (* TODO: need environment *)

let rewrite_effects ~type_safe ~params ef =
  let all_mems =
    List.fold_left
      (fun acc v -> all_possible_memory_effects acc v.vi_region v.vi_type)
      MemorySet.empty
      params
  in
  if not type_safe
  then ef
  else
    { ef with
      e_memories =
        MemoryMap.(fold
          (fun (mc, r) labs acc ->
            match mc with
            | JCmem_field _
            | JCmem_plain_union _ ->
              add (mc, r) labs acc
            | JCmem_bitvector ->
              MemorySet.fold
                (fun (mc', r') acc ->
                   if Region.equal r r'
                   then add (mc', r') labs acc
                   else acc)
                all_mems
                acc)
          ef.e_memories
          empty)
    }

let any_value' ty =
  let any_fun =
    let typ = ty.lt_name in
    let open Name.Type in
    if typ = alloc_table then "any_alloc_table"
    else if typ = tag_table then "any_tag_table"
    else if typ = memory then "any_memory"
    else invalid_arg "any_value: requested any avalue of unsupported type"
  in
  make_app ~ty:(Base_type ty) any_fun [void]

let define_locals ?(reads=[]) ?(writes=[]) e' =
  let e' = List.fold_left (fun acc (n, ty') -> mk_expr (Let (n, any_value' ty', acc))) e' reads in
  let e' = List.fold_left (fun acc (n, ty') -> mk_expr (Let_ref (n, any_value' ty', acc))) e' writes in
  e'

(******************************************************************************)
(*                                 Structures                                 *)
(******************************************************************************)

(* Conversion to and from bitvector *)

let make_param ~name ~writes ~reads ~pre ~post ~return_type =
  (* parameters and effects *)
  let write_effects = List.map effect_of_parameter writes in
  let write_params = List.map wparam_of_parameter writes in
  let read_params = List.map rparam_of_parameter reads in
  let params = write_params @ read_params in
  let params = List.map local_of_parameter params in
  (* type *)
  let annot_type =
    Annot_type(
      pre,
      Base_type return_type,
      (* reads and writes *)
      [], write_effects,
      (* normal post *)
      post,
      (* no exceptional post *)
      [])
  in
  let annot_type = List.fold_right (fun (n, ty') acc -> Prod_type (n, ty', acc)) params annot_type in
  Param (false, id_no_loc name, annot_type)

let conv_bw_alloc_parameters ~deref r _pc =
  let ac = JCalloc_bitvector in
  let allocv =
    if deref
    then alloc_table_var ~test_current_function:true (ac, r)
    else plain_alloc_table_var (ac, r)
  in
  let alloc = (allocv, alloc_table_type ac) in
  [alloc]

let conv_bw_mem_parameters ~deref r _pc =
  let mc = JCmem_bitvector in
  let memv =
    if deref
    then memory_var ~test_current_function:true (mc, r)
    else plain_memory_var (mc, r)
  in
  let mem = memv, memory_type mc in
  [mem]

let conv_typ_alloc_parameters r (* pc *) =
  function
  | JCtag _ as pc ->
    let ac = alloc_class_of_pointer_class pc in
    let alloc = plain_alloc_table_var (ac, r), alloc_table_type ac in
    [alloc]
  | JCroot vi ->
    let ac = JCalloc_root vi in
    let alloc = plain_alloc_table_var (ac, r), alloc_table_type ac in
    [alloc]

let conv_typ_mem_parameters ~deref r (* pc *) =
  let memvar = if deref then deref_memory_var else plain_memory_var in
  function
  | JCtag _ as pc ->
    let all_mems = all_memories pc in
    List.map (fun mc -> memvar (mc, r), memory_type mc) all_mems
  | JCroot rt ->
    match rt.ri_kind with
    | Rvariant -> []
    | RdiscrUnion -> Options.jc_error Why_loc.dummy_position "Unsupported discriminated union" (* TODO *)
    | RplainUnion ->
      let mc = JCmem_plain_union rt in
      let mem = memvar (mc, r), memory_type mc in
      [mem]

let make_ofbit_alloc_param_app r pc =
  let writes = conv_typ_alloc_parameters r pc in
  let reads = conv_bw_alloc_parameters ~deref:true r pc in
  let args = List.map fst writes @ List.map fst reads in
  let app =
    match pc with
    | JCtag _ ->
      make_app (alloc_of_bitvector_param_name pc) args
    | JCroot rt ->
      match rt.ri_kind with
      | Rvariant -> void
      | RdiscrUnion -> Options.jc_error Why_loc.dummy_position "Unsupported discriminated union" (* TODO *)
      | RplainUnion -> Options.jc_error Why_loc.dummy_position "Unsupported plain union" (* TODO *)
  in
  let locals = List.map local_of_parameter writes in
  locals, app

let make_ofbit_mem_param_app r pc =
  let writes = conv_typ_mem_parameters ~deref:false r pc in
  let reads = conv_bw_mem_parameters ~deref:true r pc in
  let args = List.map fst writes @ List.map fst reads in
  let app =
    match pc with
    | JCtag _ ->
      make_app (mem_of_bitvector_param_name pc) args
    | JCroot rt ->
      match rt.ri_kind with
      | Rvariant -> void
      | RdiscrUnion -> Options.jc_error Why_loc.dummy_position "Unsupported discriminated union" (* TODO *)
      | RplainUnion -> Options.jc_error Why_loc.dummy_position "Unsupported plain union" (* TODO *)
  in
  let locals = List.map local_of_parameter writes in
  locals, app

let make_tobit_alloc_param_app r pc =
  let writes = conv_bw_alloc_parameters ~deref:false r pc in
  let reads = conv_typ_alloc_parameters r pc in
  let args = List.map fst writes @ List.map fst reads in
  let app =
    match pc with
    | JCtag _ ->
      make_app (alloc_to_bitvector_param_name pc) args
    | JCroot rt ->
      match rt.ri_kind with
      | Rvariant -> void
      | RdiscrUnion -> Options.jc_error Why_loc.dummy_position "Unsupported discriminated union" (* TODO *)
      | RplainUnion -> Options.jc_error Why_loc.dummy_position "Unsupported plain union" (* TODO *)
  in
  app

let make_tobit_mem_param_app r pc =
  let writes = conv_bw_mem_parameters ~deref:false r pc in
  let reads = conv_typ_mem_parameters ~deref:true r pc in
  let args = List.map fst writes @ List.map fst reads in
  let app =
    match pc with
    | JCtag _ ->
      make_app (mem_to_bitvector_param_name pc) args
    | JCroot rt ->
      match rt.ri_kind with
      | Rvariant -> void
      | RdiscrUnion -> Options.jc_error Why_loc.dummy_position "Unsupported discriminated union" (* TODO *)
      | RplainUnion -> Options.jc_error Why_loc.dummy_position "Unsupported plain union" (* TODO *)
  in
  app

let make_of_bitvector_app fi e' =
  (* Convert bitvector into appropriate type *)
  match fi.fi_type with
  | JCTenum ri -> LApp (logic_enum_of_bitvector_name ri, [e'])
  | JCTpointer (pc, _, _) ->
    LApp (logic_variant_of_bitvector_name (pointer_class_root pc), [e'])
  | _ty ->
    Options.jc_error Why_loc.dummy_position "Unsupported type of field %s.%s" fi.fi_hroot.si_name fi.fi_name (* TODO *)

let make_conversion_params pc =
  let p = "p" in
  let bv_mem = Name.Generic.memory JCmem_bitvector in
  let bv_alloc = Name.Generic.alloc_table JCalloc_bitvector in

  (* postcondition *)
  let post_alloc = match pc with
    | JCtag(st,_) ->
        if struct_has_size st then
          let post_alloc =
            let ac = alloc_class_of_pointer_class pc in
            let alloc = Name.Generic.alloc_table ac in
            let s = string_of_int (struct_size_in_bytes st) in
            let post_min =
              make_eq_pred integer_type
                (LApp("offset_min",[ LVar alloc; LVar p ]))
                (LApp("offset_min_bytes",[ LVar bv_alloc;
                                           LApp("pointer_address",[ LVar p ]);
                                           LConst(Prim_int s)]))
            in
            let post_max =
              make_eq_pred integer_type
                (LApp("offset_max",[ LVar alloc; LVar p ]))
                (LApp("offset_max_bytes",[ LVar bv_alloc;
                                           LApp("pointer_address",[ LVar p ]);
                                           LConst(Prim_int s)]))
            in
            let ty' = pointer_type ac pc in
            let post = make_and post_min post_max in
            LForall(p,ty',[],post)
          in
          post_alloc
        else LTrue
    | JCroot _ -> assert false (* TODO *)
  in
  let post_mem = match pc with
    | JCtag(st,_) ->
        if struct_has_size st then
          let fields = all_fields pc in
          let post_mem,_ =
            List.fold_left
              (fun (acc,i) fi ->
                 if field_type_has_bitvector_representation fi then
                   let pi = p ^ (string_of_int i) in
                   let mc = JCmem_field fi in
                   let ac = alloc_class_of_mem_class mc in
                   let mem =
                     tmemory_var ~label_in_name:true LabelHere
                       (mc,dummy_region)
                   in
                   let off =
                     match field_offset_in_bytes fi with
                       | Some x -> x
                       | None ->
                          Typing.typing_error
                            Why_loc.dummy_position
                            "Field %s of structure %s \
has bitvector representation, but its bit offset (%d) is not a multiple of 8. \
The axioms for pointer-arithmetic operations with pointers to structure %s \
thus turn out to be considerably hard and are currently unsupported."
                          fi.fi_name
                          st.si_name
                          (field_offset fi)
                          st.si_name
                   in
                   let size =
                     match fi.fi_bitsize with
                       | Some x -> x / 8
                       | None ->
                           Typing.typing_error
                             Why_loc.dummy_position
                             "Field %s of structure %s \
has bitvector representation, but its bit size is unknown. \
Can't encode proper axioms for accessing the field."
                          fi.fi_name
                          st.si_name
                          st.si_name
                   in
                   let off = string_of_int off and size = string_of_int size in
                   let posti =
                     make_eq_pred fi.fi_type
                       (LApp("select",[ mem; LVar pi ]))
                       (make_of_bitvector_app fi
                          (LApp("select_bytes",
                                [ LVar bv_mem;
                                  LApp("pointer_address",[ LVar pi ]);
                                  LConst(Prim_int off); LConst(Prim_int size) ])))
                   in
                   let ty' = pointer_type ac pc in (* Correct pc *)
                   let posti = LForall(pi,ty',[],posti) in
                   make_and acc posti, i+1
                 else acc, i
              ) (LTrue,0) fields
          in
          post_mem
        else LTrue
    | JCroot _ -> assert false (* TODO *)
  in

  (* Invariant linking typed and byte views *)

(*   let mem_logic = *)
(*     Logic(false, mem_bitvector_logic_name pc, params, result_ty')  *)
(*   in *)

  (* Conversion from bitvector *)
  let writes = conv_typ_alloc_parameters dummy_region pc in
  let reads = conv_bw_alloc_parameters ~deref:true dummy_region pc in
  let name = alloc_of_bitvector_param_name pc in
  let alloc_ofbit_param =
    make_param ~name ~writes ~reads ~pre:LTrue ~post:post_alloc
      ~return_type:why_unit_type
  in

  let writes = conv_typ_mem_parameters ~deref:false dummy_region pc in
  let reads = conv_bw_mem_parameters ~deref:true dummy_region pc in
  let name = mem_of_bitvector_param_name pc in
  let mem_ofbit_param =
    make_param ~name ~writes ~reads ~pre:LTrue ~post:post_mem
      ~return_type:why_unit_type
  in

  (* Conversion to bitvector *)
  let writes = conv_bw_alloc_parameters ~deref:false dummy_region pc in
  let reads = conv_typ_alloc_parameters dummy_region pc in
  let name = alloc_to_bitvector_param_name pc in
  let alloc_tobit_param =
    make_param ~name ~writes ~reads ~pre:LTrue ~post:post_alloc
      ~return_type:why_unit_type
  in

  let writes = conv_bw_mem_parameters ~deref:false dummy_region pc in
  let reads = conv_typ_mem_parameters ~deref:true dummy_region pc in
  let name = mem_to_bitvector_param_name pc in
  let mem_tobit_param =
    make_param ~name ~writes ~reads ~pre:LTrue ~post:post_mem
      ~return_type:why_unit_type
  in

  [ alloc_ofbit_param; mem_ofbit_param; alloc_tobit_param; mem_tobit_param ]


(******************************************************************************)
(*                               call arguments                               *)
(******************************************************************************)

type param_mode = [ `MAppParam | `MFunParam ]
type effect_mode = [ `MEffect | `MLocalEffect ]
type param_or_effect_mode = [ param_mode | effect_mode ]
type param_or_local_mode = [ param_mode | `MLocal ]
type param_or_effect_or_local_mode = [ param_or_effect_mode | `MLocal ]

let remove_duplicates ~already_used entries =
  fst (List.fold_left
         (fun (acc,already_used) entry ->
            (* Accumulate entry only if not already present *)
            let n = var_name' (fst (snd entry)) in
            if StringSet.mem n already_used then
              acc, already_used
            else
              entry :: acc, StringSet.add n already_used
         ) ([],already_used) entries)

let check_no_duplicates ~already_used entries =
  ignore (List.fold_left
            (fun already_used entry ->
               (* Check entry not already present *)
               let n = var_name' (fst (snd entry)) in
               assert (not (StringSet.mem n already_used));
               StringSet.add n already_used
            ) already_used entries)

let add_alloc_table_argument
    ~mode ~type_safe ~no_deref (ac,distr as alloc) ?region_assoc acc =
  let allocvar =
    if no_deref then plain_alloc_table_var
    else alloc_table_var ~test_current_function:false
  in
  let ty' = alloc_table_type ac in
  if Region.polymorphic distr then
    try
      (* Polymorphic allocation table. Both passed in argument by the caller,
         and counted as effect. *)
      let locr =
        Option.map_default ~f:(RegionList.assoc distr) ~default:distr region_assoc
      in
      match mode with
        | `MAppParam ->
            if Region.bitwise locr && not no_deref then
              (* Anticipate generation of local ref from bitwise *)
              ((alloc,locr), (deref_alloc_table_var (ac,locr), ty')) :: acc
            else
              ((alloc,locr), (allocvar (ac,locr), ty')) :: acc
        | `MFunParam | #effect_mode ->
            if Region.bitwise locr && not type_safe then
              (* Bitwise allocation table in the caller.
                 Translate the allocation class. *)
              let ac = JCalloc_bitvector in
              let ty' = alloc_table_type ac in
              ((alloc,locr), (allocvar (ac,locr), ty')) :: acc
            else
              ((alloc,locr), (allocvar (ac,locr), ty')) :: acc
        | `MLocal -> acc
    with Not_found ->
      (* MLocal allocation table. Neither passed in argument by the caller,
         nor counted as effect. *)
      match mode with
        | #param_or_effect_mode -> acc
        | `MLocal ->
            if Region.bitwise distr && not type_safe then
              (* Bitwise allocation table. Translate the allocation class. *)
              let ac = JCalloc_bitvector in
              let ty' = alloc_table_type ac in
              ((alloc,distr), (allocvar (ac,distr), ty')) :: acc
            else
              ((alloc,distr), (allocvar (ac,distr), ty')) :: acc
  else
    (* Constant allocation table. Not passed in argument by the caller,
       but counted as effect. *)
    match mode with
      | #param_or_local_mode -> acc
      | #effect_mode -> ((alloc,distr), (allocvar (ac,distr), ty')) :: acc

let translate_alloc_table_effects ~region_mem_assoc alloc_effect =
  AllocMap.fold
    (fun (ac,r) labs acc ->
       let allocs = transpose_alloc_table ~region_mem_assoc (ac,r) in
       AllocSet.fold
         (fun (ac,_r) acc -> AllocMap.add (ac,r) labs acc) allocs acc
    ) alloc_effect AllocMap.empty

(* let translate_external_alloc_tables ~no_deref ~region_mem_assoc ~already_used *)
(*     allocs = *)
(*   let already_used = StringSet.of_list already_used in *)
(*   let allocvar =  *)
(*     if no_deref then plain_alloc_table_var  *)
(*     else alloc_table_var ~test_current_function:false *)
(*   in *)
(*   let allocs = *)
(*     List.fold_left *)
(*       (fun acc ((alloc,locr),(v',ty') as entry) -> *)
(*       if Region.bitwise locr then *)
(*         (\* Translate bitwise allocation table into typed ones *\) *)
(*         try *)
(*           let mems = MemorySet.find_region locr region_mem_assoc in *)
(*           let allocs =  *)
(*             List.map *)
(*               (fun (mc,_r) -> *)
(*                  let ac = alloc_class_of_mem_class mc in *)
(*                  let ty' = alloc_table_type ac in *)
(*                  ((alloc,locr), (allocvar (ac,locr), ty')) *)
(*               ) (MemorySet.elements mems) *)
(*           in allocs @ acc *)
(*         with Not_found -> *)
(*           (\* No possible effect on caller types *\) *)
(*           acc *)
(*       else entry :: acc *)
(*       ) [] allocs *)
(*   in *)
(*   remove_duplicates ~already_used allocs *)

let alloc_table_detailed_writes ~mode ~type_safe ~callee_writes ?region_assoc
    ~region_mem_assoc =
  let write_effects = callee_writes.e_alloc_tables in
  let write_effects =
    if type_safe then
      match mode with
        | #param_mode | `MEffect ->
            translate_alloc_table_effects ~region_mem_assoc write_effects
      | `MLocalEffect | `MLocal -> write_effects
    else write_effects
  in
  let writes =
    AllocMap.fold
      (fun (ac,distr) _labs acc ->
         add_alloc_table_argument
           ~mode ~type_safe ~no_deref:true (ac,distr) ?region_assoc acc
      ) write_effects []
  in
  if type_safe then
    writes
  else
    remove_duplicates ~already_used:StringSet.empty writes

let alloc_table_writes ~mode ~type_safe ~callee_writes ?region_assoc
    ~region_mem_assoc =
  List.map snd
    (alloc_table_detailed_writes ~mode ~type_safe ~callee_writes ?region_assoc
       ~region_mem_assoc)

let alloc_table_detailed_reads ~mode ~type_safe ~callee_writes ~callee_reads
    ?region_assoc ~region_mem_assoc ~already_used =
  let read_effects = callee_reads.e_alloc_tables in
  let read_effects =
    if type_safe then
      match mode with
        | #param_mode | `MEffect ->
            translate_alloc_table_effects ~region_mem_assoc read_effects
        | `MLocalEffect | `MLocal -> read_effects
    else read_effects
  in
  let reads =
    AllocMap.fold
      (fun (ac,distr) _labs acc ->
         if has_alloc_table (ac,distr) callee_writes.e_alloc_tables then
           (* Allocation table is written, thus it is already taken care of
              as a parameter. *)
           match mode with
             | #param_or_local_mode -> acc
             | #effect_mode ->
                 add_alloc_table_argument
                   ~mode ~type_safe ~no_deref:false (ac,distr) ?region_assoc acc
         else if mutable_alloc_table (get_current_function ()) (ac,distr) then
           add_alloc_table_argument
             ~mode ~type_safe ~no_deref:false (ac,distr) ?region_assoc acc
         else
           (* Allocation table is immutable, thus it is not passed by
              reference. As such, it cannot be counted in effects. *)
           match mode with
             | #param_or_local_mode ->
                 add_alloc_table_argument
                   ~mode ~type_safe ~no_deref:false (ac,distr) ?region_assoc acc
             | #effect_mode -> acc
      ) read_effects []
  in
  if type_safe then
    reads
  else
    let already_used = StringSet.of_list already_used in
    remove_duplicates ~already_used reads

let alloc_table_reads ~mode ~type_safe ~callee_writes ~callee_reads
    ?region_assoc ~region_mem_assoc ~already_used =
  List.map snd
    (alloc_table_detailed_reads ~mode ~type_safe ~callee_writes ~callee_reads
       ?region_assoc ~region_mem_assoc ~already_used)

let add_tag_table_argument ~mode ~no_deref (vi,distr) ?region_assoc acc =
  let tagvar = if no_deref then plain_tag_table_var else tag_table_var in
  let ty' = tag_table_type vi in
  if Region.polymorphic distr then
    try
      (* Polymorphic tag table. Both passed in argument by the caller,
         and counted as effect. *)
      let locr =
        Option.map_default ~f:(RegionList.assoc distr) ~default:distr region_assoc
      in
      match mode with
        | #param_or_effect_mode -> (tagvar (vi,locr), ty') :: acc
        | `MLocal -> acc
    with Not_found ->
      (* MLocal tag table. Neither passed in argument by the caller,
         nor counted as effect. *)
      match mode with
        | #param_or_effect_mode -> acc
        | `MLocal -> (tagvar (vi,distr), ty') :: acc
  else
    (* Constant tag table. Not passed in argument by the caller,
       but counted as effect. *)
    match mode with
      | #param_or_local_mode -> acc
      | #effect_mode -> (tagvar (vi,distr), ty') :: acc

let tag_table_writes ~mode ~callee_writes ?region_assoc () =
  TagMap.fold
    (fun (vi,distr) _labs acc ->
       add_tag_table_argument
         ~mode ~no_deref:true (vi,distr) ?region_assoc acc
    ) callee_writes.e_tag_tables []

let tag_table_reads ~mode ~callee_writes ~callee_reads ?region_assoc () =
  TagMap.fold
    (fun (vi,distr) _labs acc ->
       if TagMap.mem (vi,distr) callee_writes.e_tag_tables then
         (* Tag table is written, thus it is already taken care of
            as a parameter. *)
         match mode with
           | #param_or_local_mode -> acc
           | #effect_mode ->
               add_tag_table_argument
                 ~mode ~no_deref:false (vi,distr) ?region_assoc acc
       else if mutable_tag_table (get_current_function ()) (vi,distr) then
         add_tag_table_argument
           ~mode ~no_deref:false (vi,distr) ?region_assoc acc
       else
         (* Tag table is immutable, thus it is not passed by
            reference. As such, it cannot be counted in effects. *)
         match mode with
           | #param_or_local_mode ->
               add_tag_table_argument
                 ~mode ~no_deref:false (vi,distr) ?region_assoc acc
           | #effect_mode -> acc
    ) callee_reads.e_tag_tables []

let add_memory_argument
    ~mode ~type_safe ~no_deref (mc,distr as mem) ?region_assoc acc =
  let memvar =
    if no_deref then plain_memory_var
    else memory_var ~test_current_function:false
  in
  let ty' = memory_type mc in
  if Region.polymorphic distr then
    try
      (* Polymorphic memory. Both passed in argument by the caller,
         and counted as effect. *)
      let locr =
        Option.map_default ~f:(RegionList.assoc distr) ~default:distr region_assoc
      in
      match mode with
        | `MAppParam ->
            if Region.bitwise locr && not no_deref then
              (* Anticipate generation of local ref from bitwise *)
              ((mem,locr), (deref_memory_var (mc,locr), ty')) :: acc
            else
              ((mem,locr), (memvar (mc,locr), ty')) :: acc
        | `MFunParam | #effect_mode ->
            if Region.bitwise locr && not type_safe then
              (* Bitwise memory in the caller.
                 Translate the memory class. *)
              let mc = JCmem_bitvector in
              let ty' = memory_type mc in
              ((mem,locr), (memvar (mc,locr), ty')) :: acc
            else
              ((mem,locr), (memvar (mc,locr), ty')) :: acc
        | `MLocal -> acc
    with Not_found ->
      (* MLocal memory. Neither passed in argument by the caller,
         nor counted as effect. *)
      match mode with
        | #param_or_effect_mode -> acc
        | `MLocal ->
            if Region.bitwise distr && not type_safe then
              (* Bitwise memory. Translate the memory class. *)
              let mc = JCmem_bitvector in
              let ty' = memory_type mc in
              ((mem,distr), (memvar (mc,distr), ty')) :: acc
            else
              ((mem,distr), (memvar (mc,distr), ty')) :: acc
  else
    (* Constant memory. Not passed in argument by the caller,
       but counted as effect. *)
    match mode with
      | #param_or_local_mode -> acc
      | #effect_mode -> ((mem,distr), (memvar (mc,distr), ty')) :: acc

(* let translate_external_memories ~no_deref ~region_mem_assoc ~already_used mems = *)
(*   let already_used = StringSet.of_list already_used in *)
(*   let memvar =  *)
(*     if no_deref then plain_memory_var  *)
(*     else memory_var ~test_current_function:false *)
(*   in *)
(*   let mems = *)
(*     List.fold_left *)
(*       (fun acc ((mem,locr),(v',ty') as entry) -> *)
(*       if Region.bitwise locr then *)
(*         try *)
(*           (\* Translate bitwise memories into typed ones *\) *)
(*           let mems = MemorySet.find_region locr region_mem_assoc in *)
(*           let mems =  *)
(*             List.map *)
(*               (fun (mc,_r) -> *)
(*                  let ty' = memory_type mc in *)
(*                  ((mem,locr), (memvar (mc,locr), ty')) *)
(*               ) (MemorySet.elements mems) *)
(*           in mems @ acc *)
(*         with Not_found -> *)
(*           (\* No possible effect on caller types *\) *)
(*           acc *)
(*       else entry :: acc *)
(*       ) [] mems *)
(*   in *)
(*   remove_duplicates ~already_used mems *)

let translate_memory_effects ~region_mem_assoc mem_effect =
  MemoryMap.fold
    (fun (mc,r) labs acc ->
       let mems = transpose_memory ~region_mem_assoc (mc,r) in
       MemorySet.fold
         (fun (mc,_r) acc -> MemoryMap.add (mc,r) labs acc) mems acc
    ) mem_effect MemoryMap.empty

let memory_detailed_writes
    ~mode ~type_safe ~callee_writes ?region_assoc ~region_mem_assoc =
  let write_effects = callee_writes.e_memories in
  let write_effects =
    if type_safe then
      match mode with
        | #param_mode | `MEffect ->
            translate_memory_effects ~region_mem_assoc write_effects
        | `MLocalEffect | `MLocal -> write_effects
    else write_effects
  in
  let writes =
    MemoryMap.fold
      (fun (mc,distr) _labs acc ->
         add_memory_argument
           ~mode ~type_safe ~no_deref:true (mc,distr) ?region_assoc acc
      ) write_effects []
  in
  if type_safe then
    (* non-interference precondition added later on *)
(*     let () = check_no_duplicates ~already_used:StringSet.empty writes in *)
    writes
  else
    remove_duplicates ~already_used:StringSet.empty writes

let memory_writes
    ~mode ~type_safe ~callee_writes ?region_assoc ~region_mem_assoc =
  List.map snd
    (memory_detailed_writes ~mode ~type_safe ~callee_writes
       ?region_assoc ~region_mem_assoc)

let memory_detailed_reads ~mode ~type_safe ~callee_writes ~callee_reads
    ?region_assoc ~region_mem_assoc ~already_used =
  let read_effects = callee_reads.e_memories in
  let read_effects =
    if type_safe then
      match mode with
        | #param_mode | `MEffect ->
            translate_memory_effects ~region_mem_assoc read_effects
        | `MLocalEffect | `MLocal -> read_effects
    else read_effects
  in
  let write_effects = callee_writes.e_memories in
  let write_effects =
    if type_safe then
      match mode with
        | #param_mode | `MEffect ->
            translate_memory_effects ~region_mem_assoc write_effects
        | `MLocalEffect | `MLocal -> write_effects
    else write_effects
  in
  let reads =
    MemoryMap.fold
      (fun (mc,distr) _labs acc ->
         if has_memory (mc,distr) write_effects then
           (* Memory is written, thus it is already taken care of
              as a parameter. *)
           match mode with
             | #param_or_local_mode -> acc
             | #effect_mode ->
                 add_memory_argument
                   ~mode ~type_safe ~no_deref:false (mc,distr) ?region_assoc acc
         else if mutable_memory (get_current_function ()) (mc,distr) then
           add_memory_argument
             ~mode ~type_safe ~no_deref:false (mc,distr) ?region_assoc acc
         else
           (* Memory is immutable, thus it is not passed by
              reference. As such, it cannot be counted in effects. *)
           match mode with
             | #param_or_local_mode ->
                 add_memory_argument
                   ~mode ~type_safe ~no_deref:false (mc,distr) ?region_assoc acc
             | #effect_mode -> acc
      ) read_effects []
  in
  let already_used = StringSet.of_list already_used in
  if type_safe then
    (* non-interference precondition added later on *)
(*     let () = check_no_duplicates ~already_used reads in *)
    reads
  else
    remove_duplicates ~already_used reads

let memory_reads ~mode ~type_safe ~callee_writes ~callee_reads
    ?region_assoc ~region_mem_assoc ~already_used =
  List.map snd
    (memory_detailed_reads ~mode ~type_safe ~callee_writes ~callee_reads
       ?region_assoc ~region_mem_assoc ~already_used)

let global_writes ~callee_writes =
  VarMap.fold
    (fun v _labs acc ->
       let n,ty' = param ~type_safe:false v in
       (plain_var n,ty') :: acc
    ) callee_writes.e_globals []

let global_reads ~callee_reads =
  VarMap.fold
    (fun v _labs acc ->
       let n,ty' = param ~type_safe:false v in
       (plain_var n,ty') :: acc
    ) callee_reads.e_globals []

let local_reads ~callee_reads =
  VarMap.fold
    (fun v _labs acc ->
       let n,ty' = param ~type_safe:false v in
       (plain_var n,ty') :: acc
    ) callee_reads.e_locals []

(* Yannick: change this to avoid recovering the real type from its name
   in mutable and committed effects *)

let write_mutable callee_writes =
  StringSet.fold
    (fun v acc -> (mutable_name2 v)::acc) callee_writes.e_mutable []

let read_mutable callee_reads =
  StringSet.fold
    (fun v acc -> (mutable_name2 v)::acc) callee_reads.e_mutable []

let write_committed callee_writes =
  StringSet.fold
    (fun v acc -> (committed_name2 v)::acc) callee_writes.e_committed []

let read_committed callee_reads =
  StringSet.fold
    (fun v acc -> (committed_name2 v)::acc) callee_reads.e_committed []

let make_region_assoc region_list =
  List.map (fun r -> (r,r)) region_list

let write_model_parameters
    ~type_safe ~mode ~callee_reads ~callee_writes ?region_list ~params () =
  assert (same_effects callee_reads callee_reads);
  let region_assoc = Option.map make_region_assoc region_list in
  let region_mem_assoc = make_region_mem_assoc ~params in
  let callee_writes = rewrite_effects ~type_safe ~params callee_writes in
  let write_allocs =
    alloc_table_writes ~mode ~type_safe ~callee_writes
      ?region_assoc ~region_mem_assoc
  in
  let write_tags =
    tag_table_writes ~mode ~callee_writes ?region_assoc ()
  in
  let write_mems =
    memory_writes ~mode ~type_safe ~callee_writes
      ?region_assoc ~region_mem_assoc
  in
  let write_globs = match mode with
    | #param_or_local_mode -> []
    | #effect_mode -> global_writes ~callee_writes
  in
  (* TODO: add mutable and committed effects *)
  write_allocs @ write_tags @ write_mems @ write_globs

let write_parameters
    ~type_safe ~region_list ~callee_reads ~callee_writes ~params =
  let vars' =
    write_model_parameters ~type_safe ~mode:`MFunParam
      ~callee_reads ~callee_writes ~region_list ~params ()
  in
  List.map (function ({expr_node = Var n},ty') -> (n,ty') | _ -> assert false) vars'

let write_locals ~region_list ~callee_reads ~callee_writes ~params =
  let vars' =
    write_model_parameters ~type_safe:false ~mode:`MLocal
      ~callee_reads ~callee_writes ~region_list ~params ()
  in
  List.map (function ({expr_node = Var n},ty') -> (n,ty') | _ -> assert false) vars'

let write_effects ~callee_reads ~callee_writes ~region_list ~params =
  let vars' =
    write_model_parameters ~type_safe:true ~mode:`MEffect
      ~callee_reads ~callee_writes ~region_list ~params ()
  in
  List.map (function ({expr_node = Var n},_ty') -> n | _ -> assert false) vars'

let local_write_effects ~callee_reads ~callee_writes =
  let vars' =
    write_model_parameters ~type_safe:false ~mode:`MLocalEffect
      ~callee_reads ~callee_writes ~params:[] ()
  in
  List.map (var_name' % fst) vars'

let read_model_parameters ~type_safe ~mode ~callee_reads ~callee_writes
    ?region_list ~params ~already_used () =
  let region_assoc = Option.map make_region_assoc region_list in
  let region_mem_assoc = make_region_mem_assoc ~params in
  let callee_reads = rewrite_effects ~type_safe ~params callee_reads in
  let callee_writes = rewrite_effects ~type_safe ~params callee_writes in
  let read_allocs =
    alloc_table_reads ~mode ~type_safe ~callee_reads ~callee_writes
      ?region_assoc ~region_mem_assoc ~already_used
  in
  let read_tags =
    tag_table_reads ~mode ~callee_reads ~callee_writes ?region_assoc ()
  in
  let read_mems =
    memory_reads ~mode ~type_safe ~callee_reads ~callee_writes
      ?region_assoc ~region_mem_assoc ~already_used
  in
  let read_globs = match mode with
    | #param_or_local_mode -> []
    | #effect_mode -> global_reads ~callee_reads
  in
  let read_locs = match mode with
    | #param_or_local_mode | `MEffect -> []
    | `MLocalEffect -> local_reads ~callee_reads
  in
  (* TODO: add mutable and committed effects *)
  read_allocs @ read_tags @ read_mems @ read_globs @ read_locs

let read_parameters
    ~type_safe ~region_list ~callee_reads ~callee_writes ~params ~already_used =
  let vars' =
    read_model_parameters ~type_safe ~mode:`MFunParam
      ~callee_reads ~callee_writes ~region_list ~params ~already_used ()
  in
  List.map (function ({expr_node = Var n},ty') -> (n,ty') | _ -> assert false) vars'

let read_locals ~region_list ~callee_reads ~callee_writes ~params =
  let vars' =
    read_model_parameters ~type_safe:false ~mode:`MLocal
      ~callee_reads ~callee_writes ~region_list ~params ~already_used:[] ()
  in
  List.map (function ({expr_node = Var n},ty') -> (n,ty')
              | ({expr_node = Deref n},ty') ->
                  printf "Deref %s with type %a@." n Output.fprintf_logic_type ty';
                  assert false
              | _ -> assert false
           ) vars'

let read_effects ~callee_reads ~callee_writes ~region_list ~params =
  let vars' =
    read_model_parameters ~type_safe:true ~mode:`MEffect
      ~callee_reads ~callee_writes ~region_list ~params ~already_used:[] ()
  in
  List.map (var_name' % fst) vars'

let local_read_effects ~callee_reads ~callee_writes =
  let vars' =
    read_model_parameters ~type_safe:false ~mode:`MLocalEffect
      ~callee_reads ~callee_writes ~params:[] ~already_used:[] ()
  in
  List.map (var_name' % fst) vars'

let alloc_table_arguments ~callee_reads ~callee_writes ~region_assoc
    ~region_mem_assoc =
  let writes =
    alloc_table_detailed_writes
      ~mode:`MAppParam ~type_safe:true ~callee_writes
      ~region_assoc ~region_mem_assoc
  in
  let reads =
    alloc_table_detailed_reads
      ~mode:`MAppParam ~type_safe:true ~callee_reads ~callee_writes
      ~region_assoc ~region_mem_assoc ~already_used:[]
  in
  let pointer_of_parameter = function
      (((ac,_distr),locr),(_v',_ty')) ->
        let pc = match ac with
          | JCalloc_root vi -> JCroot vi
          | JCalloc_bitvector -> assert false
        in
        (pc,locr)
  in
  let wpointers = List.map pointer_of_parameter writes in
  let rpointers = List.map pointer_of_parameter reads in
  let write_arguments = List.map (fst % snd) writes in
  let read_arguments = List.map (fst % snd) reads in
  wpointers, rpointers, write_arguments, read_arguments

let tag_table_arguments ~callee_reads ~callee_writes ~region_assoc =
  let writes =
    tag_table_writes ~mode:`MAppParam ~callee_writes ~region_assoc ()
  in
  let reads =
    tag_table_reads
      ~mode:`MAppParam ~callee_reads ~callee_writes ~region_assoc ()
  in
  (List.map fst writes), (List.map fst reads)

let specialized_functions = StringHashtblIter.create 0

let memory_arguments ~callee_reads ~callee_writes ~region_assoc
    ~region_mem_assoc ~param_assoc ~with_body fname =
  let writes =
    memory_detailed_writes
      ~mode:`MAppParam ~type_safe:true ~callee_writes
      ~region_assoc ~region_mem_assoc
  in
  let reads =
    memory_detailed_reads
      ~mode:`MAppParam ~type_safe:true ~callee_reads ~callee_writes
      ~region_assoc ~region_mem_assoc ~already_used:[]
  in
  let pointer_of_parameter = function
      (((mc,_distr),locr),(_v',_ty')) ->
        let pc = match mc with
          | JCmem_field fi -> JCtag(fi.fi_struct,[])
          | JCmem_plain_union vi -> JCroot vi
          | JCmem_bitvector -> assert false
        in
        (pc,locr)
  in
  let wpointers = List.map pointer_of_parameter writes in
  let rpointers = List.map pointer_of_parameter reads in
  let remove_local effects =
    List.map (fun ((mem,_locr),(v',ty')) -> (mem,(v',ty'))) effects
  in
  let writes' = remove_local writes and reads' = remove_local reads in
  (* Check if there are duplicates between reads and writes *)
  let write_names = List.map (var_name' % fst % snd) writes in
  let read_names = List.map (var_name' % fst % snd) reads in
  let rw_inter_names =
    StringSet.inter
      (StringSet.of_list write_names) (StringSet.of_list read_names)
  in
  let rw_pre =
    if StringSet.is_empty rw_inter_names then
      LTrue (* no read/write interference *)
    else if not with_body then
      LTrue (* no body in which region assumptions must be verified *)
    else
      write_read_separation_condition
        ~callee_reads ~callee_writes ~region_assoc ~param_assoc
        rw_inter_names writes' reads'
  in
  (* TODO: rewrite postcondition to assert it after the call, when
     there is an interference. see, e.g., example [separation.c] in Jessie
     tests.
  *)
  (* Check if there are duplicates between writes *)
  let ww_inter_names =
    snd (List.fold_left
           (fun (first_occur,next_occur) n ->
              if StringSet.mem n first_occur then
                first_occur, StringSet.add n next_occur
              else StringSet.add n first_occur, next_occur
           ) (StringSet.empty,StringSet.empty) write_names)
  in
  let ww_pre =
    if StringSet.is_empty ww_inter_names then
      LTrue (* no write/write interference *)
    else if not with_body then
      LTrue (* no body in which region assumptions must be verified *)
    else
      write_write_separation_condition
        ~callee_reads ~callee_writes ~region_assoc ~param_assoc
        ww_inter_names writes' reads'
  in
  let pre = make_and rw_pre ww_pre in
  if pre = LTrue then
    let writes = List.map (fst % snd) writes in
    let reads = List.map (fst % snd) reads in
    LTrue, fname, wpointers, rpointers, writes, reads
  else
    (* Presence of interferences. Function must be specialized. *)
    let new_fname = unique_name (fname ^ "_specialized") in
    let writes, name_assoc, already_used_names =
      List.fold_right
        (fun ((mc,distr),(v,_ty)) (acc,name_assoc,already_used_names) ->
           let n = var_name' v in
           if StringMap.mem n already_used_names then
             let ndest = StringMap.find n already_used_names in
             let nsrc = memory_name (mc,distr) in
             acc, StringMap.add nsrc ndest name_assoc, already_used_names
           else
             let ndest = memory_name (mc,distr) in
             v :: acc, name_assoc, StringMap.add n ndest already_used_names
        ) writes' ([], StringMap.empty, StringMap.empty)
    in
    let reads, name_assoc, _ =
      List.fold_right
        (fun ((mc,distr),(v,_ty)) (acc,name_assoc,already_used_names) ->
           let n = var_name' v in
           if StringMap.mem n already_used_names then
             let ndest = StringMap.find n already_used_names in
             let nsrc = memory_name (mc,distr) in
             acc, StringMap.add nsrc ndest name_assoc, already_used_names
           else
             let ndest = memory_name (mc,distr) in
             v :: acc, name_assoc, StringMap.add n ndest already_used_names
        ) reads' ([], name_assoc, already_used_names)
    in
    StringHashtblIter.add specialized_functions new_fname (fname,name_assoc);
    pre, new_fname, wpointers, rpointers, writes, reads

let global_arguments ~callee_reads ~callee_writes ~region_assoc:_ =
  let writes = global_writes ~callee_writes in
  let reads = global_reads ~callee_reads in
  (List.map fst writes), (List.map fst reads)

(* Identify bitwise arguments and generate appropriate typed ones *)
let make_bitwise_arguments alloc_wpointers alloc_rpointers
    mem_wpointers mem_rpointers =
  let bw_pointers pointers =
    PointerSet.of_list (List.filter (Region.bitwise % snd) pointers)
  in
  let bw_alloc_wpointers = bw_pointers alloc_wpointers in
  let bw_alloc_rpointers = bw_pointers alloc_rpointers in
  let bw_alloc_pointers =
    PointerSet.union bw_alloc_wpointers bw_alloc_rpointers
  in
  let bw_mem_wpointers = bw_pointers mem_wpointers in
  let bw_mem_rpointers = bw_pointers mem_rpointers in
  let bw_mem_pointers =
    PointerSet.union bw_mem_wpointers bw_mem_rpointers
  in
  let bw_pointers =
    PointerSet.union bw_alloc_pointers bw_mem_pointers
  in

  let locals,prolog,epilog =
    List.fold_left
      (fun (acc,pro,epi) (pc,r as pointer) ->
         let alloc_locals,alloc_ofapp =
           if PointerSet.mem_region r bw_alloc_pointers then
             make_ofbit_alloc_param_app r pc
           else [], void
         in
         let mem_locals,mem_ofapp =
           if PointerSet.mem pointer bw_mem_pointers then
             make_ofbit_mem_param_app r pc
           else [], void
         in
         let alloc_toapp =
           if PointerSet.mem_region r bw_alloc_wpointers then
             make_tobit_alloc_param_app r pc
           else void
         in
         let mem_toapp =
           if PointerSet.mem pointer bw_mem_wpointers then
             make_tobit_mem_param_app r pc
           else void
         in
         let locals = alloc_locals @ mem_locals in
         let ofapp = append alloc_ofapp mem_ofapp in
         let toapp = append alloc_toapp mem_toapp in
         locals @ acc, append ofapp pro, append toapp epi
      ) ([],void,void) (PointerSet.to_list bw_pointers)
  in
  let locals =
    fst (List.fold_left
           (fun (acc,already_used) entry ->
              (* Accumulate entry only if not already present *)
              let n = fst entry in
              if StringSet.mem n already_used then
                acc, already_used
              else
                entry :: acc, StringSet.add n already_used
           ) ([],StringSet.empty) locals)
  in
  locals,prolog,epilog

let make_arguments
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc
    ~with_globals ~with_body fname args =
  let params = List.map fst param_assoc in
  let region_mem_assoc = make_region_mem_assoc ~params in
  let alloc_wpointers, alloc_rpointers, write_allocs, read_allocs =
    alloc_table_arguments ~callee_reads ~callee_writes ~region_assoc
      ~region_mem_assoc
  in
  let write_tags, read_tags =
    tag_table_arguments ~callee_reads ~callee_writes ~region_assoc
  in
  let pre_mems, fname, mem_wpointers, mem_rpointers, write_mems, read_mems =
    memory_arguments ~callee_reads ~callee_writes ~region_assoc
      ~region_mem_assoc ~param_assoc ~with_body fname
  in
  let write_globs, read_globs =
    if with_globals then
      global_arguments ~callee_reads ~callee_writes ~region_assoc
    else
      [], []
  in
  let locals, prolog, epilog =
    make_bitwise_arguments alloc_wpointers alloc_rpointers
      mem_wpointers mem_rpointers
  in
  (* Return complete list of arguments *)
  (* TODO: add mutable and committed effects *)
  let args =
    args
    @ write_allocs @ write_tags @ write_mems @ write_globs
    @ read_allocs @ read_tags @ read_mems @ read_globs
  in
  pre_mems, fname, locals, prolog, epilog, args

(*******************************************************************************)
(* Logic arguments translation                                                 *)
(*******************************************************************************)

let tr_li_model_arg_3 is_mutable get_name get_type ~label_in_name lab (c, _ as cr) =
  let name = get_name cr in
  let constant =
    match !current_function with
    | None -> true
    | Some f -> not (is_mutable f cr)
  in
  lvar_name ~label_in_name lab name,
  lvar ~constant ~label_in_name lab name,
  get_type c

let tr_li_model_mem_arg_3, tr_li_model_at_arg_3, tr_li_model_tt_arg_3 =
  let tr = tr_li_model_arg_3 in
  tr mutable_memory      memory_name              memory_type,
  tr mutable_alloc_table Name.alloc_table      alloc_table_type,
  tr mutable_tag_table   Name.tag_table        tag_table_type

let tr_li_model_args_5 fold tr_arg_3 get_map ~label_in_name ?region_assoc ?label_assoc reads =
  let tr_region =
    Option.(
      map_default
        ~f:(fun ra r -> transpose_region ra r)
        ~default:some
        region_assoc)
  in
  fold
    (fun (c, param_r) labs acc ->
       LogicLabelSet.fold
         (fun lab acc ->
            let arg_r, param =
              match tr_region param_r with
              | Some arg_r -> arg_r, tr_arg_3 ~label_in_name (transpose_label ~label_assoc lab) (c, arg_r)
              | None ->
                Options.jc_error
                  Why_loc.dummy_position
                  "Unable to translate logic function application: dangling region. See warnings above for more info."
            in
            ((c, arg_r), param) :: acc)
         labs
         acc)
    (get_map reads)
    []

let tr_li_model_mem_args_5, tr_li_model_at_args_5, tr_li_model_tt_args_5 =
  let tr = tr_li_model_args_5 in
  tr MemoryMap.fold tr_li_model_mem_arg_3 (fun e -> e.e_memories),
  tr AllocMap.fold  tr_li_model_at_arg_3  (fun e -> e.e_alloc_tables),
  tr TagMap.fold    tr_li_model_tt_arg_3  (fun e -> e.e_tag_tables)

let tr_li_model_mem_args_3, tr_li_model_at_args_3, tr_li_model_tt_args_3 =
  let f tr ~label_in_name ?region_assoc ?label_assoc reads =
    List.map snd @@ tr ~label_in_name ?region_assoc ?label_assoc reads
  in
  f tr_li_model_mem_args_5,
  f tr_li_model_at_args_5,
  f tr_li_model_tt_args_5

let tr_li_model_glob_args_4 ~label_in_name ?region_assoc:_ ?label_assoc reads =
  VarMap.fold
    (fun v labs acc ->
       LogicLabelSet.fold
         (fun lab acc ->
            let param = tparam ~label_in_name (transpose_label ~label_assoc lab) v in
            (v, param) :: acc)
         labs
         acc)
    reads.e_globals
    []

let tr_li_model_glob_args_3 ~label_in_name ?region_assoc ?label_assoc reads =
  List.map snd (tr_li_model_glob_args_4 ~label_in_name ?region_assoc ?label_assoc reads)

let tr_li_model_args_3 ~label_in_name ?region_assoc ?label_assoc reads =
  let tr f = f ~label_in_name ?region_assoc ?label_assoc reads in
  tr tr_li_model_at_args_3 @
  tr tr_li_model_tt_args_3 @
  tr tr_li_model_mem_args_3 @
  tr tr_li_model_glob_args_3

let tr_li_args ~label_in_name ~region_assoc ~label_assoc f args =
  args @
  List.map (fun (_, term, _) -> term) @@
    tr_li_model_args_3 ~label_in_name ~region_assoc ~label_assoc f.li_effects

let tr_logic_fun_call ~label_in_name ~region_assoc ~label_assoc f args =
  if Options.debug then printf "logic call to %s@." f.li_name;
  let args = tr_li_args ~label_in_name ~region_assoc ~label_assoc f args in
  LApp (f.li_final_name, args)

let tr_logic_pred_call ~label_in_name ~region_assoc ~label_assoc f args =
  if Options.debug then printf "logic pred call to %s@." f.li_name;
  let args = tr_li_args ~label_in_name ~region_assoc ~label_assoc f args in
  LPred (f.li_final_name, args)

let collect_li_reads acc li =
  let add fold get_name get_map acc =
    fold
      (fun cr _ -> StringSet.add @@ get_name cr)
      (get_map li.li_effects)
      acc
  in
  acc |>
  add MemoryMap.fold memory_name         (fun e -> e.e_memories) |>
  add AllocMap.fold  Name.alloc_table (fun e -> e.e_alloc_tables) |>
  add TagMap.fold    Name.tag_table   (fun e -> e.e_tag_tables)


(* fold all effects into a list *)
let all_effects ef =
  let res =
    MemoryMap.fold
      (fun (mc,r) _labels acc ->
        let mem = memory_name(mc,r) in
        if Region.polymorphic r then
(*        if RegionList.mem r f.fun_param_regions then
            if FieldRegionMap.mem (fi,r)
              f.fun_effects.fe_writes.e_memories
            then mem::acc
            else acc
          else acc*)
          assert false (* TODO *)
        else mem::acc)
      ef.e_memories
      []
  in
  let res =
    VarMap.fold
      (fun v _labs acc -> v.vi_final_name::acc)
      ef.e_globals
      res
  in
  let res =
    AllocMap.fold
      (fun (a,r) _labs acc ->
        let alloc = Name.alloc_table (a, r) in
        if Region.polymorphic r then
(*        if RegionList.mem r f.fun_param_regions then
            if AllocSet.mem (a,r)
              f.fun_effects.fe_writes.e_alloc_tables
            then alloc::acc
            else acc
          else acc*)
          assert false (* TODO *)
        else alloc::acc)
      ef.e_alloc_tables
      res
  in
  let res =
    TagMap.fold
      (fun v _ acc -> (Name.tag_table v)::acc)
      ef.e_tag_tables
      res
  in
  let res =
    StringSet.fold
      (fun v acc -> (mutable_name2 v)::acc)
      ef.e_mutable
      res
  in
  let res =
    StringSet.fold
      (fun v acc -> (committed_name2 v)::acc)
      ef.e_committed
      res
  in
  res


(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_interp_misc.ml"
  End:
*)
