open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Output

(* other modifications for this extension can be found in:
     ast, typing, norm, interp: about pack / unpack, and mutable
     jc_main.ml
       phase 3.5
       production phase 5
     jc_interp.ml
       function tr_fun: 2 calls to "assume_all_invariants"
       function statement
         JCSassign_heap: call to "assume_field_invariants"
     jc_typing.ml
       hashtbl mutable_fields_table
       hashtbl committed_fields_table
       function create_mutable_field
       function find_field_struct: "mutable" and "committed" cases (and the parameter allow_mutable)
       function decl: JCPDstructtype: call to create_mutable_field
       function statement: call to "assert_mutable"

TODOs:
     Maybe generate assocs (or global invariant) when doing unpack or pack, as it modifies
mutable and committed.
     Arrays and global invariant.
*)

(********)
(* Misc *)
(********)

(* same as in jc_interp.ml *)
let tag_name st = st.jc_struct_info_name ^ "_tag"

(* same as in jc_interp.ml *)
let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }

(* same as in jc_interp.ml *)
let logic_params li l =
  let l =
    FieldSet.fold
      (fun fi acc -> (LVar fi.jc_field_info_name)::acc)
      li.jc_logic_info_effects.jc_effect_memories
      l	    
  in
  let l = 
    StringSet.fold
      (fun v acc -> (LVar (v ^ "_alloc_table"))::acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      l	    
  in
  StringSet.fold
    (fun v acc -> (LVar (v ^ "_tag_table"))::acc)
    li.jc_logic_info_effects.jc_effect_tag_table
    l	    

(* same as in jc_interp.ml *)
let make_logic_fun_call li l =
  let params = logic_params li l in
  LApp(li.jc_logic_info_name,params)

(* same as in jc_interp.ml *)
let make_logic_pred_call li l =
  let params = logic_params li l in
  LPred(li.jc_logic_info_name,params)

(* will be set by jc_interp.ml (defining modules recursively is not possible in separate files) *)
let memory_field' = ref (fun _ -> raise (Failure "memory_field in jc_invariants.ml should be set by jc_interp.ml"))
let memory_field x = !memory_field' x

let prop_type = simple_logic_type "prop"

let memory_type st_type f_type = {
  logic_type_name = "memory";
  logic_type_args = [
    simple_logic_type st_type;
    f_type;
  ];
}

let pointer_type st_type = {
  logic_type_name = "pointer";
  logic_type_args = [
    simple_logic_type st_type;
  ];
}

let tag_type root = {
  logic_type_name = "tag_id";
  logic_type_args = [
    simple_logic_type root;
  ];
}

let tag_table_type root = {
  logic_type_name = "tag_table";
  logic_type_args = [
    simple_logic_type root
  ]
}

let logic_info_reads acc li =
  let acc =
    FieldSet.fold
      (fun fi acc -> StringSet.add fi.jc_field_info_name acc)
      li.jc_logic_info_effects.jc_effect_memories
      acc
  in
  let acc =
    StringSet.fold
      (fun v acc -> StringSet.add (v^"_alloc_table") acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      acc
  in
  StringSet.fold
    (fun v acc -> StringSet.add (v^"_tag_table") acc)
    li.jc_logic_info_effects.jc_effect_tag_table
    acc

(* returns (inv, reads) where i is the assertion of the invariants of the structure
and r is a StringSet of the "reads" needed by these invariants *)
let invariant_for_struct this st =
  let (_, invs) = Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name in
  let inv =
    make_and_list
      (List.map (fun (li, _) -> make_logic_pred_call li [this]) invs)
  in
  let reads =
    List.fold_left
      (fun acc (li, _) -> logic_info_reads acc li)
      StringSet.empty
      invs
  in
  (inv, reads)

let make_assume reads assume =
  BlackBox (Annot_type (LTrue, unit_type, reads, [], assume, []))

let mutable_name root_structure_name =
  "mutable_"^root_structure_name

let committed_name root_structure_name =
  "committed_"^root_structure_name

let fully_packed_name root =
  "fully_packed_"^root

let tag_table_name root =
  root^"_tag_table"

let make_subtag t u =
  LPred("subtag", [ t; u ])

let fully_packed root e =
  LPred(
    "fully_packed",
    [ LVar (tag_table_name root);
      LVar (mutable_name root);
      e ])

let type_structure = function
  | JCTpointer(st, _, _) -> st
  | _ -> failwith "type_structure"

let hierarchy_invariant_name h = "global_invariant_"^h

(*let mutable_instance_of_name root_structure_name =
  (mutable_name root_structure_name)^"_instance_of"*)

(************************************)
(* Checking an invariant definition *)
(************************************)

(* Typing imposes non pointer fields to have the flag "rep" *)
let field fi this loc =
  if not fi.jc_field_info_rep then
    Jc_typing.typing_error loc "this term is not a rep field of %s" this.jc_var_info_name

let rec check_rep ?(must_deref=false) this loc t =
  match t.jc_term_node with
    | JCTvar vi when vi == this && not must_deref -> ()
    | JCTderef (t, fi) ->
	field fi this loc;
	check_rep ~must_deref:false this loc t
    | JCTcast (t, _)
    | JCTshift (t, _) ->
	(* t must not be this, but might be a field of this if it is a table (? TODO) *)
	check_rep ~must_deref:true this loc t
    | _ ->
	Jc_typing.typing_error loc "this term is not a rep field of %s" this.jc_var_info_name

let rec term this t =
  match t.jc_term_node with
    | JCTconst _ -> ()
    | JCTif (_, _, _) -> assert false (* TODO *)
    | JCTcast (t, _) -> term this t
    | JCTinstanceof (t, _) -> term this t
    | JCToffset(_, t, _) -> term this t
    | JCTold t
    | JCTunary (_,t) -> term this t
    | JCTapp (id, l) ->
	if FieldSet.is_empty id.jc_logic_info_effects.jc_effect_memories
	then List.iter (term this) l
	else
	  Jc_typing.typing_error t.jc_term_loc
	    "this call is not allowed in structure invariant"
    | JCTderef _ ->
	check_rep this t.jc_term_loc t
    | JCTshift (t1, t2) 
    | JCTsub_pointer (t1, t2) 
    | JCTrange (t1, t2)
    | JCTbinary(t1,_,t2) -> term this t1; term this t2
    | JCTvar _ -> ()

let tag this t =
  match t.jc_tag_node with
    | JCTtag _
    | JCTbottom -> ()
    | JCTtypeof(t, _) -> term this t

let rec assertion this p =
  match p.jc_assertion_node with
    | JCAtrue | JCAfalse -> ()
    | JCAif (_, _, _) -> assert false (* TODO *)
    | JCAinstanceof(t,_)
    | JCAbool_term t -> term this t
    | JCAold p -> assertion this p
    | JCAquantifier(_,id, p) -> assertion this p
    | JCAapp (id, l) ->
	if FieldSet.is_empty id.jc_logic_info_effects.jc_effect_memories
	then List.iter (term this) l
	else
	  Jc_typing.typing_error p.jc_assertion_loc
	    "this call is not allowed in structure invariant"
    | JCAnot p -> assertion this p
    | JCAiff (p1, p2)
    | JCAimplies (p1, p2) -> assertion this p1; assertion this p2
    | JCArelation (t1,_, t2) -> term this t1; term this t2
    | JCAand l | JCAor l -> List.iter (assertion this) l
    | JCAmutable _ ->
	Jc_typing.typing_error p.jc_assertion_loc
	  "\\mutable is not allowed in structure invariant"
    | JCAtagequality(t1, t2, _) ->
	tag this t1;
	tag this t2

let check invs =
  List.iter
    (fun (li,p) -> 
       match li.jc_logic_info_parameters with
	 | [this] -> assertion this p
	 | _ -> assert false)
    invs

(***********************************)
(* Tools for structure definitions *)
(***********************************)

let rec term_memories aux t = match t.jc_term_node with
  | JCTconst _
  | JCTvar _ -> aux
  | JCTshift(t1, t2)
  | JCTsub_pointer(t1, t2)
  | JCTrange(t1,t2) 
  | JCTbinary(t1,_,t2) -> term_memories (term_memories aux t1) t2
  | JCTderef(t, fi) ->
      let m = fi.jc_field_info_name in
      term_memories (StringSet.add m aux) t
  | JCTapp(_, l) -> List.fold_left term_memories aux l
  | JCTold t
  | JCToffset(_,t, _)
  | JCTinstanceof(t, _)
  | JCTcast(t, _) 
  | JCTunary(_,t) -> term_memories aux t
  | JCTif(t1, t2, t3) -> term_memories (term_memories (term_memories aux t1) t2) t3

let tag_memories aux t = match t.jc_tag_node with
  | JCTtag _ | JCTbottom -> aux
  | JCTtypeof(t, _) -> term_memories aux t

let rec assertion_memories aux a = match a.jc_assertion_node with
  | JCAtrue
  | JCAfalse -> aux
  | JCAand l
  | JCAor l -> List.fold_left assertion_memories aux l
  | JCAimplies(a1, a2)
  | JCAiff(a1, a2) -> assertion_memories (assertion_memories aux a1) a2
  | JCArelation(t1,_,t2) -> term_memories (term_memories aux t1) t2
  | JCAnot a
  | JCAold a
  | JCAquantifier(_,_, a) -> assertion_memories aux a
  | JCAapp(_, l) -> List.fold_left term_memories aux l
  | JCAinstanceof(t, _)
  | JCAbool_term t -> term_memories aux t
  | JCAif(t, a1, a2) -> assertion_memories (assertion_memories (term_memories aux t) a1) a2
  | JCAmutable(t, _, _) -> term_memories aux t
  | JCAtagequality(t1, t2, _) -> tag_memories (tag_memories aux t2) t1

(* Returns (as a StringSet.t) every structure name that can be reached from st.
Assumes the structures whose name is in acc have already been visited
and won't be visited again. *)
let rec all_structures st acc =
  if StringSet.mem st.jc_struct_info_name acc then acc else
  begin
    List.fold_left
      (fun acc (_, fi) ->
	 match fi.jc_field_info_type with
	   | JCTpointer(st, _, _) -> all_structures st acc
	   | _ -> acc)
      (StringSet.add st.jc_struct_info_name acc)
      st.jc_struct_info_fields
  end

(* Returns all memories used by the structure invariants. *)
let struct_inv_memories acc st =
  let _, invs = Hashtbl.find Jc_typing.structs_table st in
  List.fold_left
    (fun acc (_, a) -> assertion_memories acc a)
    acc
    invs

(* Returns the parameters needed by an invariant, "this" not included *)
let invariant_params acc li =
  let acc =
    FieldSet.fold
      (fun fi acc -> 
	 (fi.jc_field_info_name, memory_field fi)::acc)
      li.jc_logic_info_effects.jc_effect_memories
      acc
  in
  let acc =
    StringSet.fold
      (fun v acc -> 
	 let t = { logic_type_args = [simple_logic_type v];
		   logic_type_name = "alloc_table" }
	 in
	 (v ^ "_alloc_table", t)::acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      acc
  in
  let acc =
    StringSet.fold
      (fun v acc -> 
	 let t = { logic_type_args = [simple_logic_type v];
		   logic_type_name = "tag_table" }
	 in
	 (v ^ "_tag_table", t)::acc)
      li.jc_logic_info_effects.jc_effect_tag_table
      acc
  in
    acc

(* Returns the parameters needed by the invariants of a structure, "this" not included *)
let invariants_params acc st =
  let (_, invs) = Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name in
  List.fold_left (fun acc (li, _) -> invariant_params acc li) acc invs

(* Returns the structure and its parents, up to its root *)
let rec parents acc st =
  match st.jc_struct_info_parent with
    | None -> acc
    | Some p -> parents (st::acc) p
let parents = parents []

(* Returns every structure (name) that can be used by a function, given its parameters *)
let function_structures params =
  (* structures that can be used by the function *)
  let structures = List.fold_left
    (fun acc vi ->
       match vi.jc_var_info_type with
	 | JCTpointer(st, _, _) ->
	     all_structures st acc
	 | _ -> acc)
    StringSet.empty
    params
  in
  StringSet.elements structures

let hierarchy_structures h =
  Hashtbl.fold
    (fun _ (st, _) acc -> if st.jc_struct_info_root = h then st::acc else acc)
    Jc_typing.structs_table
    []
  
let structure_root st =
  try
    let st, _ = Hashtbl.find Jc_typing.structs_table st in
    st.jc_struct_info_root
  with Not_found -> failwith "Jc_invariants.structure_root"

let hierarchies () =
  let h = Hashtbl.fold
    (fun _ (st, _) acc -> StringSet.add st.jc_struct_info_root acc)
    Jc_typing.structs_table
    StringSet.empty
  in StringSet.elements h

(* Returns every rep fields of a structure *)
let rep_fields st =
  List.filter
    (fun (_, fi) -> fi.jc_field_info_rep)
    st.jc_struct_info_fields


(*********)
(* assoc *)
(*********)

(*let program_point_type = simple_logic_type "int"

let fresh_program_point =
  let c = ref 0 in fun () ->
  c := !c + 1; string_of_int !c

let assoc_declaration =
  (* logic assoc: int, ('a, 'b) memory -> prop *)
  Logic(
    false,
    "assoc",
    [ "", program_point_type;
      "", memory_type "'a" (simple_logic_type "'b") ],
    prop_type)

let make_assoc pp m =
  LPred("assoc", [LConst(Prim_int pp); LVar m])

let make_assoc_list pp mems =
  make_and_list (List.map (make_assoc pp) mems)

let make_assume_assocs pp mems =
  let assocs = make_assoc_list pp mems in
  make_assume mems assocs

(* List of each memory m that appears in an invariant
which can be broken by the modification of the field fi *)
let field_assocs fi =
  let _, invs = Hashtbl.find Jc_typing.structs_table fi.jc_field_info_root in
  let mems = List.fold_left
    (fun aux (_, a) ->
       let amems = assertion_memories StringSet.empty a in
       if StringSet.mem fi.jc_field_info_name amems then
         StringSet.union amems aux
       else
	 aux
    ) (StringSet.singleton (mutable_name fi.jc_field_info_root)) invs in
  StringSet.elements mems

(* Assume all assocs needed after a field has been modified *)
let make_assume_field_assocs pp fi =
  make_assume_assocs pp (field_assocs fi)

(* Returns a list of all memories which need an "assoc"
(calculated from a function parameter list) *)
let all_assocs pp params =
  let structures = function_structures params in
  (* memories used by these structures' invariants *)
  let memories = List.fold_left
    struct_inv_memories
    StringSet.empty
    structures
  in
  (* mutable fields *)
  let mutable_fields = List.map (fun s -> mutable_name s) structures in
  StringSet.elements memories@mutable_fields

(* Assume all assocs needed at the start of a fonction *)
let make_assume_all_assocs pp params =
  make_assume_assocs pp (all_assocs pp params)*)

(***********)
(* mutable *)
(***********)

let mutable_memory_type root =
  memory_type root (tag_type root)

let committed_memory_type root =
  memory_type root (simple_logic_type "bool")

let mutable_declaration st acc =
  let root = st.jc_struct_info_root in
  if st.jc_struct_info_parent = None then
    (* mutable_T: T tag_id *)
    Param(
      false,
      mutable_name st.jc_struct_info_name,
      Ref_type(Base_type (mutable_memory_type root)))
    (* committed_T: bool *)
    ::Param(
      false,
      committed_name st.jc_struct_info_name,
      Ref_type(Base_type (committed_memory_type root)))
    ::acc
  else
    acc

(* Assert the condition under which a field update statement can be executed.
The object must be "sufficiently unpacked", that is: its "mutable" field is
a strict superclass of the class in which the field is defined.
  And the object must not be committed. *)
(* assert ((st.jc_struct_info_parent <: e.mutable || e.mutable = bottom_tag) && e.committed = false) *)
(* Actually, the "not committed" part is meta-implied by the
condition on mutable. *)
let assert_mutable e fi =
  if fi.jc_field_info_rep then
    begin
      let st, _ = Hashtbl.find Jc_typing.structs_table fi.jc_field_info_struct in
      let mutable_name = mutable_name st.jc_struct_info_root in
      (*let committed_name = committed_name st.jc_struct_info_root in*)
      let e_mutable = LApp("select", [LVar mutable_name; e]) in
      (*let e_committed = LApp("select", [LVar committed_name; e]) in*)
      let parent_tag = match st.jc_struct_info_parent with
	| None -> LVar "bottom_tag"
	| Some parent -> LVar (tag_name parent)
      in
      let sub = make_subtag parent_tag e_mutable in
      (*let not_committed =
	LPred(
	  "eq",
	  [ e_committed;
	    LConst (Prim_bool false) ])
      in
      Assert(make_and sub not_committed, Void)*)
      Assert(sub, Void)
    end
  else
    Void

(********************)
(* Invariant axioms *)
(********************)

(*let invariant_axiom st acc (li, a) =
  let params = invariant_params [] li in
  
  (* this *)
  let this = "this" in
  let this_ty =
    { logic_type_name = "pointer";
      logic_type_args = [simple_logic_type st.jc_struct_info_root] } in

  (* program point *)
  let pp = "program_point" in
  let pp_ty = simple_logic_type "int" in

  (* assoc memories with program point => not this.mutable => this.invariant *)
  let mutable_ty = mutable_memory_type st.jc_struct_info_root in
  let mutable_is_false =
    LPred(
      "eq",
      [ LConst(Prim_bool false);
	LApp("select", [LVar "mutable"; LVar this]) ]) in
  let assoc_memories = StringSet.fold
    (fun mem acc ->
       LPred("assoc", [LVar pp; LVar mem])::acc)
    (assertion_memories
       (StringSet.singleton "mutable")
       a)
    [] in
  let invariant = make_logic_pred_call li [LVar this] in
  let axiom_impl = List.fold_left (fun acc assoc -> LImpl(assoc, acc))
    (LImpl(mutable_is_false, invariant))
    assoc_memories in

  (* quantifiers *)
  let quantified_vars = params in
  let quantified_vars = ("mutable", mutable_ty)::quantified_vars in
  let quantified_vars = (pp, pp_ty)::quantified_vars in
  let quantified_vars = (this, this_ty)::quantified_vars in
  let axiom =
    List.fold_left (fun acc (id, ty) -> LForall(id, ty, acc))
      axiom_impl quantified_vars in
  Axiom("axiom_"^li.jc_logic_info_name, axiom)::acc

let invariants_axioms st acc =
  let _, invs = Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name in
  List.fold_left (invariant_axiom st) acc invs*)

(******************************************)
(* Invariant assumes (axioms pre-applied) *)
(******************************************)

(* hierarchy root (string) -> hierarchy invariant parameters ((string * logic_type) list) *)
let hierarchy_invariants = Hashtbl.create 97

(* List of each invariant that can be broken by modifying a given field *)
let field_invariants fi =
  if not fi.jc_field_info_rep then [] else (* small optimisation, it is not needed *)
    (* List of all structure * invariant *)
    let invs = Hashtbl.fold
      (fun _ (st, invs) acc -> (List.map (fun inv -> st, inv) invs)@acc)
      Jc_typing.structs_table
      []
    in
    (* Only keep the invariants which uses the field *)
    List.fold_left
      (fun aux ((_, (_, a)) as x) ->
	 let amems = assertion_memories StringSet.empty a in
	 if StringSet.mem fi.jc_field_info_name amems then
           x::aux
	 else
	 aux)
      []
      invs

(* this.mutable <: st => invariant *)
(* (the invariant li must be declared in st) *)
let not_mutable_implies_invariant this st (li, _) =
  let params = invariant_params [] li in
  let root = st.jc_struct_info_root in
  
  (* this.mutable <: st *)
  let mutable_name = mutable_name root in
  let mutable_io = make_subtag
    (LApp("select", [ LVar mutable_name; LVar this ]))
    (LVar (tag_name st))
  in

  (* invariant *)
  let invariant = make_logic_pred_call li [LVar this] in

  (* implies *)
  let impl = LImpl(mutable_io, invariant) in

  (* params *)
  let params = (mutable_name, mutable_memory_type root)::params in
  let params = (tag_table_name root, tag_table_type root)::params in

  params, impl

(* this.mutable <: st => this.fields.committed *)
let not_mutable_implies_fields_committed this st =
  let root = st.jc_struct_info_root in
  let fields = rep_fields st in

  (* this.mutable <: st *)
  let mutable_name = mutable_name root in
  let mutable_io = make_subtag
    (LApp("select", [ LVar mutable_name; LVar this ]))
    (LVar (tag_name st))
  in

  (* fields committed *)
  let fields_pc = List.fold_left
    (fun acc (n, fi) ->
       match fi.jc_field_info_type with
	 | JCTpointer(fi_st, _, _) ->
	     let fi_root = fi_st.jc_struct_info_root in
	     let committed_name = committed_name fi_root in
	     let params =
	       [ n, memory_field fi;
		 committed_name, committed_memory_type fi_root ]
	     in
	     let f = LApp("select", [ LVar n; LVar this ]) in
	     let com =
	       LPred(
		 "eq",
		 [ LApp("select", [ LVar committed_name; f ]);
		   LConst(Prim_bool true) ])
	     in
	     (params, com)::acc
	 | _ -> acc)
    [] fields
  in
  let params, coms = List.flatten (List.map fst fields_pc), make_and_list (List.map snd fields_pc) in

  (* additional params *)
  let params = (mutable_name, mutable_memory_type root)::params in
  let params = (tag_table_name root, tag_table_type root)::params in

  (* implies *)
  let impl = LImpl(mutable_io, coms) in

  params, impl

(* this.committed => fully_packed(this) *)
let committed_implies_fully_packed this root =
  let committed_name = committed_name root in
  let committed_type = committed_memory_type root in
  let mutable_name = mutable_name root in
  let mutable_type = mutable_memory_type root in
  let tag_table = tag_table_name root in
  let tag_table_type = tag_table_type root in

  (* this.committed = true *)
  let com = LPred(
    "eq",
    [ LApp(
	"select",
	[ LVar committed_name;
	  LVar this ]);
      LConst(Prim_bool true) ])
  in

  (* fully_packed(this) *)
  let packed = LPred(
    "fully_packed",
    [ LVar tag_table;
      LVar mutable_name;
      LVar this ])
  in

  (* implies *)
  let impl = LImpl(com, packed) in

  (* params *)
  let params = [
    tag_table, tag_table_type;
    committed_name, committed_type;
    mutable_name, mutable_type;
  ] in

  params, impl

let lex2 (a1, b1) (a2, b2) =
  let c = compare a1 a2 in
  if c = 0 then compare b1 b2 else c

let make_hierarchy_global_invariant acc root =
  (* this *)
  let this = "this" in
  let this_ty =
    { logic_type_name = "pointer";
      logic_type_args = [simple_logic_type root] } in

  (* not mutable => invariant, and their parameters *)
  let structs = hierarchy_structures root in
  let mut_inv = List.map
    (fun st ->
       let _, invs = Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name in
       List.map (fun inv -> not_mutable_implies_invariant this st inv) invs)
    structs
  in
  let mut_inv = List.flatten mut_inv in
  let params, mut_inv = List.map fst mut_inv, List.map snd mut_inv in
  let mut_inv = make_and_list mut_inv in

  (* not mutable for T => fields defined in T committed *)
  let params, mut_com = List.fold_left
    (fun (params, coms) st ->
       let p, c = not_mutable_implies_fields_committed this st in
       p@params, make_and c coms)
    (List.flatten params, LTrue)
    structs
  in

  (* committed => fully packed *)
  let params_cfp, com_fp = committed_implies_fully_packed this root in
  let params = params_cfp@params in

  (* predicate body, quantified on "this" *)
  let body = LForall(this, this_ty, make_and_list [ mut_inv; mut_com; com_fp ]) in

  (* sort the parameters and only keep one of each *)
  let params = List.fold_left
    (fun acc (n, t) -> StringMap.add n t acc)
    StringMap.empty
    params
  in
  let params = StringMap.fold (fun n t acc -> (n, t)::acc) params [] in
  let params = List.sort lex2 params in

  (* fill hash table *)
  Hashtbl.add hierarchy_invariants root params;

  (* return the predicate *)
  match params with
    | [] -> acc (* Not supposed to happen though *)
    | _ -> Predicate(false, hierarchy_invariant_name root, params, body)::acc

let make_global_invariants acc =
  let h = hierarchies () in
  List.fold_left make_hierarchy_global_invariant acc h

let assume_global_invariant root =
  let params =
    try
      Hashtbl.find hierarchy_invariants root
    with Not_found -> failwith ("Jc_invariants.assume_global_invariant: "^root^" not found")
  in
  match params with
    | [] -> Void
    | _ ->
	let reads = List.map fst params in
	let params = List.map (fun (n, _) -> LVar n) params in
	let inv = LPred(hierarchy_invariant_name root, params) in
	make_assume reads inv

let assume_global_invariants hl =
  List.fold_left append Void (List.map assume_global_invariant hl)

(* Given a field that has just been modified, assume all potentially
useful invariant for all objects that is not mutable *)
let assume_field_invariants fi =
  let invs = field_invariants fi in
  (* keep hierarchies only once *)
  let hl = List.fold_left
    (fun acc (st, _) -> StringSet.add st.jc_struct_info_root acc)
    StringSet.empty
    invs
  in
  assume_global_invariants (StringSet.elements hl)

(* Given the parameters of a function, assume all potentially useful
forall this: st, not this.mutable => invariant *)
let assume_all_invariants params =
  let structures = function_structures params in
  (* keep hierarchies only once *)
  let hl = List.fold_left
    (fun acc st -> StringSet.add (structure_root st) acc)
    StringSet.empty
    structures
  in
  assume_global_invariants (StringSet.elements hl)

(*(* Given a field that has just been modified, assume all potentially
useful invariant for all objects that is not mutable *)
let assume_field_invariants fi =
  (* structure in which the field is defined *)
  let st, _ = Hashtbl.find Jc_typing.structs_table fi.jc_field_info_struct in
  let assumes = List.map (fun inv -> forall_mutable_invariant st inv) (field_invariants fi) in (* FAUX (st n'est pas forcément la bonne structure !) *)
  let assumes = List.map (fun (params, inv) -> make_assume (List.map fst params) inv) assumes in
  List.fold_left append Void assumes

let rec flatten_snd = function
  | [] -> []
  | (a, l)::tl -> (List.map (fun b -> a, b) l)@(flatten_snd tl)

(* Given the parameters of a function, assume all potentially useful
forall this: st, not this.mutable => invariant *)
let assume_all_invariants params =
  let structures = function_structures params in
  let st_invs =
    List.map
      (fun id -> Hashtbl.find Jc_typing.structs_table id)
      structures
  in
  let st_invs = flatten_snd st_invs in
  let assumes = List.map (fun (st, inv) -> forall_mutable_invariant st inv) st_invs in
  let assumes = List.map (fun (params, inv) -> make_assume (List.map fst params) inv) assumes in
  List.fold_left append Void assumes*)

(*****************)
(* pack / unpack *)
(*****************)

(* return fields that are both pointers and rep fields *)
let components st =
  List.fold_left
    (fun acc (_, fi) ->
       if fi.jc_field_info_rep then
	 match fi.jc_field_info_type with
	   | JCTpointer(si, _, _) -> (fi, si)::acc
	   | _ -> acc
       else acc)
    []
    st.jc_struct_info_fields

let components_by_type st =
  let compare_structs s t =
    compare s.jc_struct_info_name t.jc_struct_info_name in
  let comps = components st in
  let comps =
    List.sort
      (fun (_, s) (_, t) -> compare_structs s t)
      comps
  in
  let rec part prev acc = function
    | [] -> [prev, acc]
    | (fi, si)::tl ->
	if compare_structs si prev = 0 then
	  part prev (fi::acc) tl
	else
	  (prev, acc)::(part si [fi] tl)
  in
  let part = function
    | [] -> []
    | (fi, si)::tl -> part si [fi] tl
  in
  part comps

(* all components have "committed" = committed *)
let make_components_postcond this st reads writes committed =
  let comps = components_by_type st in
  let writes =
    List.fold_left
      (fun acc (si, _) -> StringSet.add (committed_name si.jc_struct_info_name) acc)
      writes
      comps
  in
  let reads =
    List.fold_left
      (fun acc (_, fields) ->
	 List.fold_left
	   (fun acc fi -> StringSet.add fi.jc_field_info_name acc)
	   acc
	   fields)
      reads
      comps
  in
  let reads = StringSet.union reads writes in
  let committed_value = LConst(Prim_bool committed) in
  let postcond =
    make_and_list
      (List.map
	 (fun (si, fields) ->
	    let committed_name = committed_name si.jc_struct_info_name in
	    LPred(
	      "eq",
	      [ LVar committed_name;
		List.fold_left
		  (fun acc fi ->
		     let this_field = LApp("select", [LVar fi.jc_field_info_name; this]) in
		     LApp("store", [acc; this_field; committed_value]))
		  (LVarAtLabel(committed_name, ""))
		  fields ]))
	 comps)
  in
  postcond, reads, writes  

(* all components must have mutable = committed = false (for pack) *)
let make_components_precond this st reads =
  let comps = components st in
  let reads =
    List.fold_left
      (fun acc (fi, _) -> StringSet.add fi.jc_field_info_name acc)
      reads
      comps
  in
  let l, reads = List.fold_left
    (fun (l, reads) (fi, si) ->
       let mutable_name = mutable_name si.jc_struct_info_name in
       let committed_name = committed_name si.jc_struct_info_name in
       let this_field = LApp("select", [LVar fi.jc_field_info_name; this]) in
       let fi_st = type_structure fi.jc_field_info_type in
       let reads = StringSet.add (tag_table_name fi_st.jc_struct_info_root) reads in
       let reads = StringSet.add mutable_name reads in
       (fully_packed (fi_st.jc_struct_info_root) this_field)
       ::(LPred(
	    "eq",
	    [ LApp("select", [LVar committed_name; this_field]);
	      LConst(Prim_bool false) ]))
       ::l,
       reads)
    ([], reads)
    (components st)
  in
  make_and_list l, reads

let pack_declaration st acc =
  let this = "this" in
  let this_type = pointer_type st.jc_struct_info_root in
  let tag = "tag" in
  let tag_type = tag_type st.jc_struct_info_root in
  let name = st.jc_struct_info_root in
  let mutable_name = mutable_name name in
  let inv, reads = invariant_for_struct (LVar this) st in
  let writes = StringSet.empty in
  let components_post, reads, writes = make_components_postcond (LVar this) st reads writes true in
  let components_pre, reads = make_components_precond (LVar this) st reads in
  let reads = StringSet.add mutable_name reads in
  let writes = StringSet.add mutable_name writes in
  let requires =
    make_and_list [
      (LPred(
	 "parenttag",
	 [ LVar tag;
	   LApp("select", [LVar mutable_name; LVar this]) ]));
      inv;
      components_pre
    ]
  in
  let ensures =
    make_and
      (LPred(
	 "eq",
	 [ LVar mutable_name;
	   LApp(
	     "store",
	     [ LVarAtLabel(mutable_name, "");
	       LVar this;
	       LVar tag ])]))
      components_post
  in
  let annot_type =
    Annot_type(
      requires,
      Base_type (simple_logic_type "unit"),
      StringSet.elements reads,
      StringSet.elements writes,
      ensures,
      []
    )
  in
  if st.jc_struct_info_parent = None then
    Param(
      false,
      "pack_"^st.jc_struct_info_root,
      Prod_type(
	this,
	Base_type this_type,
	Prod_type(
	  tag,
	  Base_type tag_type,
	  annot_type
	)
      )
    )::acc
  else
    acc

(* Unlike Boogie, Jessie has "unpack to S" instead of "unpack from T" *)
let unpack_declaration st acc =
  let this = "this" in
  let this_type = pointer_type st.jc_struct_info_root in
  let tag = "tag" in
  let tag_type = tag_type st.jc_struct_info_root in
  let name = st.jc_struct_info_root in
  let mutable_name = mutable_name name in
  let committed_name = committed_name name in
  let reads = StringSet.singleton mutable_name in
  let writes = StringSet.singleton mutable_name in
  let reads = StringSet.add committed_name reads in
  let components_post, reads, writes = make_components_postcond (LVar this) st reads writes false in
  let requires =
    (* unpack this as tag: requires parenttag(this.mutable, tag) and not this.committed *)
    make_and
      (LPred(
	 "parenttag",
	 [ LApp("select", [LVar mutable_name; LVar this]);
	   LVar tag ]))
      (LPred(
	 "eq",
	 [ LConst(Prim_bool false);
	   LApp("select", [LVar committed_name; LVar this]) ]))
  in
  let ensures =
    make_and
      (LPred(
	 "eq",
	 [ LVar mutable_name;
	   LApp(
	     "store",
	     [ LVarAtLabel(mutable_name, "");
	       LVar this;
	       LVar tag ])]))
      components_post
  in
  let annot_type =
    Annot_type(
      requires,
      Base_type (simple_logic_type "unit"),
      StringSet.elements reads,
      StringSet.elements writes,
      ensures,
      []
    )
  in
  if st.jc_struct_info_parent = None then
    Param(
      false,
      "unpack_"^st.jc_struct_info_root,
      Prod_type(
	this,
	Base_type this_type,
	Prod_type(
	  tag,
	  Base_type tag_type,
	  annot_type
	)
      )
    )::acc
  else
    acc

(*********************************************************************)
(*               Using a recursively-defined predicate               *)
(*********************************************************************)
(*let valid_inv_name st = st.jc_struct_info_name ^ "_inv"

let valid_inv_axiom_name st = st.jc_struct_info_name ^ "_inv_sem"

let rec struct_depends st acc mem =
  let name = st.jc_struct_info_name in
  if StringSet.mem name mem then acc, mem else
  let acc, mem = List.fold_left (fun (acc, mem) (_, fi) -> match fi.jc_field_info_type with
      | JCTpointer(st, _, _) -> struct_depends st acc mem
      | JCTnull -> assert false
      | JCTnative _ | JCTlogic _ | JCTrange _ -> acc, mem)
    (st::acc, StringSet.add name mem) st.jc_struct_info_fields
  in
  match st.jc_struct_info_parent with
    None -> acc, mem
  | Some pst -> struct_depends pst acc mem

let struct_depends =
  let table = Hashtbl.create 97 in fun st ->
  let name = st.jc_struct_info_name in
  try Hashtbl.find table name with Not_found ->
  let result = fst (struct_depends st [] StringSet.empty) in
  Hashtbl.add table name result;
  result

(* "this" is not returned in the list of parameters of valid_inv_params *)
let valid_inv_params st =
  let deps = struct_depends st in
  let memories = List.fold_left (fun acc st ->
    List.fold_left (fun acc (name, fi) ->
      (name, memory_field fi)::acc) acc st.jc_struct_info_fields)
    [] deps in
  let params = List.fold_left invariants_params memories deps in
  let params = List.sort (fun (name1, _) (name2, _) ->
    compare name2 name1) params in
  let rec only_one prev acc = function
    [] -> acc
  | ((name, _) as x)::tl ->
      if name = prev then only_one prev acc tl
      else only_one name (x::acc) tl in
  let params = only_one "" [] params in
    params

(* generate valid_inv predicate and its axiom *)
let tr_valid_inv st acc =
  let params = valid_inv_params st in

  (**** valid_inv predicate declaration ****)
  let valid_inv_type = simple_logic_type "prop" in
  let vi_this = "???",
    { logic_type_name = "pointer" ;
      logic_type_args = [simple_logic_type st.jc_struct_info_root] } in
  let logic = Logic(false, valid_inv_name st, vi_this::params,
    valid_inv_type) in
  let acc = logic::acc in

  (**** valid_inv_sem axiom ****)
  let this = "inv_this" in
  let this_var = LVar this in
  let this_ty =
    { logic_type_name = "pointer";
      logic_type_args = [simple_logic_type st.jc_struct_info_root] } in
  let fields_valid_inv = List.map (fun (name, fi) ->
    match fi.jc_field_info_type with
    | JCTpointer(st, _, _) ->
        let params = valid_inv_params st in
        let params_var = List.map (fun (name, _) -> LVar name) params in
        LPred(valid_inv_name st,
          LApp("select", [LVar name; this_var])::params_var)
    | JCTnull -> assert false
    | JCTnative _
    | JCTlogic _
    | JCTrange _ -> LTrue) st.jc_struct_info_fields in
  let params_var = List.map (fun (name, _) -> LVar name) params in
  let sem = LIff(LPred(valid_inv_name st, this_var::params_var),
    LImpl(LPred("neq", [LVar this; LVar "null"]),
      make_and (make_and_list fields_valid_inv) (invariant_for_struct this_var st))) in
  (* parent invariant *)
  let sem = match st.jc_struct_info_parent with
    None -> sem
  | Some pst ->
      let parent_params = valid_inv_params pst in
      let parent_params_var = List.map (fun (name, _) -> LVar name) parent_params in
      make_and sem (LPred(valid_inv_name pst, this_var::parent_params_var))
  in
  (* quantifiers *)
  let sem = List.fold_left (fun acc (id, ty) ->
    LForall(id, ty, acc)) sem ((this, this_ty)::params) in
  Axiom(valid_inv_axiom_name st, sem)::acc*)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessie.byte"
End: 
*)
