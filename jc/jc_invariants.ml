open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Output

(* other modifications for this extension can be found in:
     ast, typing, norm, interp: about pack / unpack, and mutable
     jc_main.ml
       phase 6
       production phase 5
     jc_interp.ml
       function tr_fun: call to "make_assume_all_assocs"
       function statement
         JCSassign_heap: call to "make_assume_field_assoc"
     jc_typing.ml
       hashtbl mutable_fields_table
       hashtbl committed_fields_table
       function create_mutable_field
       function create_structure_tag
       function find_field_struct: "mutable" and "committed" cases (and the parameter allow_mutable)
       function decl: JCPDstructtype: call to create_mutable_field
*)

(********)
(* Misc *)
(********)

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

let tag_type st = {
  logic_type_name = "tag_id";
  logic_type_args = [
    simple_logic_type st.jc_struct_info_root;
  ];
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

(************************************)
(* Checking an invariant definition *)
(************************************)

let rec term this t =
  match t.jc_term_node with
    | JCTconst _ -> ()
    | JCTif (_, _, _) -> assert false (* TODO *)
    | JCTcast (t, ty) -> term this t
    | JCTinstanceof (t, ty) -> term this t
    | JCToffset(_,t,_) -> term this t
    | JCTold t
    | JCTunary (_,t) -> term this t
    | JCTapp (id, l) ->
	if FieldSet.is_empty id.jc_logic_info_effects.jc_effect_memories
	then List.iter (term this) l
	else
	  Jc_typing.typing_error t.jc_term_loc
	    "this call is not allowed in structure invariant"
    | JCTderef (t1, fi) -> 
	begin
	  match t1.jc_term_node with
	    | JCTvar vi when vi == this -> ()
	    | _ -> 
		Jc_typing.typing_error t.jc_term_loc
		  "this dereferencing is not allowed in structure invariant"
	end
    | JCTshift (t1, t2) 
    | JCTrange (t1, t2)
    | JCTbinary(t1,_,t2) -> term this t1; term this t2
    | JCTvar _ -> ()

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

let rec term_memories aux t = match t.jc_tterm_node with
  | JCTTconst _
  | JCTTvar _ -> aux
  | JCTTshift(t1, t2)
  | JCTTrange(t1,t2) 
  | JCTTbinary(t1,_,t2) -> term_memories (term_memories aux t1) t2
  | JCTTderef(t, fi) ->
      let m = fi.jc_field_info_name in
      term_memories (StringSet.add m aux) t
  | JCTTapp(_, l) -> List.fold_left term_memories aux l
  | JCTTold t
  | JCTToffset(_,t, _)
  | JCTTinstanceof(t, _)
  | JCTTcast(t, _) 
  | JCTTunary(_,t) -> term_memories aux t
  | JCTTif(t1, t2, t3) -> term_memories (term_memories (term_memories aux t1) t2) t3

let rec assertion_memories aux a = match a.jc_tassertion_node with
  | JCTAtrue
  | JCTAfalse -> aux
  | JCTAand l
  | JCTAor l -> List.fold_left assertion_memories aux l
  | JCTAimplies(a1, a2)
  | JCTAiff(a1, a2) -> assertion_memories (assertion_memories aux a1) a2
  | JCTArelation(t1,_,t2) -> term_memories (term_memories aux t1) t2
  | JCTAnot a
  | JCTAold a
  | JCTAquantifier(_,_, a) -> assertion_memories aux a
  | JCTAapp(_, l) -> List.fold_left term_memories aux l
  | JCTAinstanceof(t, _)
  | JCTAbool_term t -> term_memories aux t
  | JCTAif(t, a1, a2) -> assertion_memories (assertion_memories (term_memories aux t) a1) a2
  | JCTAmutable(t, _, _) -> term_memories aux t

(* Returns (as a StringSet.t) every structure name that can be reach from st.
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

(*********)
(* assoc *)
(*********)

let program_point_type = simple_logic_type "int"

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

(* Returns every structure (name) that can be used by a function, given its parameters *)
let function_structures params =
  (* structures that can be used by the function *)
  let structures = List.fold_left
    (fun acc vi ->
       match vi.jc_var_info_type with
	 | JCTpointer(st, _, _) ->
	     if st.jc_struct_info_parent = None then
	       all_structures st acc
	     else acc (* TODO *)
	 | _ -> acc)
    StringSet.empty
    params
  in
  StringSet.elements structures

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
  make_assume_assocs pp (all_assocs pp params)

(***********)
(* mutable *)
(***********)

let mutable_memory_type st =
  memory_type st.jc_struct_info_root (tag_type st)

let committed_memory_type st =
  memory_type st.jc_struct_info_root (simple_logic_type "bool")

let mutable_declaration st acc =
  if st.jc_struct_info_parent = None then
    (* mutable_T: T tag_id *)
    Param(
      false,
      mutable_name st.jc_struct_info_name,
      Ref_type(Base_type (mutable_memory_type st)))
    (* committed_T: bool *)
    ::Param(
      false,
      committed_name st.jc_struct_info_name,
      Ref_type(Base_type (committed_memory_type st)))
    ::acc
  else
    acc

let assert_mutable e fi =
(*  let mutable_name = mutable_name fi.jc_field_info_root in*)
  Assert(
(* TODO    LPred(
      "eq",
      [ LApp("select", [LVar mutable_name; e]);
	LConst(Prim_bool true) ]
    ), *)
    LTrue,
    Void
  )

(********************)
(* Invariant axioms *)
(********************)

let invariant_axiom st acc (li, a) =
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
  let mutable_ty = mutable_memory_type st in
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
  List.fold_left (invariant_axiom st) acc invs

(******************************************)
(* Invariant assumes (axioms pre-applied) *)
(******************************************)

(* List of each invariant that can be broken by modifying a given field *)
let field_invariants fi =
  let _, invs = Hashtbl.find Jc_typing.structs_table fi.jc_field_info_root in
  List.fold_left
    (fun aux (li, a) ->
       let amems = assertion_memories StringSet.empty a in
       if StringSet.mem fi.jc_field_info_name amems then
         (li, a)::aux
       else
	 aux)
    []
    invs

(* Assume that for all this: st, not this.mutable => invariant *)
let assume_invariant st (li, _) =
  let params = invariant_params [] li in
  
  (* this *)
  let this = "this" in
  let this_ty =
    { logic_type_name = "pointer";
      logic_type_args = [simple_logic_type st.jc_struct_info_root] } in

  (* not this.mutable => this.invariant *)
  let mutable_name = mutable_name st.jc_struct_info_root in
  let mutable_is_false =
    LTrue in
(* TODO   LPred(
      "eq",
      [ LConst(Prim_bool false);
	LApp("select", [LVar mutable_name; LVar this]) ]) in*)
  let invariant = make_logic_pred_call li [LVar this] in
  let assume_impl = LImpl(mutable_is_false, invariant) in

  (* quantifier (forall this) *)
  let assume = LForall(this, this_ty, assume_impl) in

  (* reads *)
  let reads = List.map fst params in
  let reads = mutable_name::reads in

  make_assume reads assume

(* Given a field that has just been modified, assume all potentially
useful invariant for all objects that is not mutable *)
let assume_field_invariants fi =
  let st, _ = Hashtbl.find Jc_typing.structs_table fi.jc_field_info_root in
  let assumes = List.map (fun inv -> assume_invariant st inv) (field_invariants fi) in
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
  let assumes = List.map (fun (st, inv) -> assume_invariant st inv) st_invs in
  List.fold_left append Void assumes

(*****************)
(* pack / unpack *)
(*****************)

let components st =
  List.fold_left
    (fun acc (_, fi) ->
       match fi.jc_field_info_type with
	 | JCTpointer(si, _, _) -> (fi, si)::acc
	 | _ -> acc)
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
(* TODO       (LPred(
	 "eq",
	 [ LApp("select", [LVar mutable_name; this_field]);
	   LConst(Prim_bool false) ]))
       ::*)(LPred(
	    "eq",
	    [ LApp("select", [LVar committed_name; this_field]);
	      LConst(Prim_bool false) ]))
       ::l,
       StringSet.add mutable_name reads)
    ([], reads)
    (components st)
  in
  make_and_list l, reads

let pack_declaration st acc =
  let this = "this" in
  let this_type = pointer_type st.jc_struct_info_root in
  let tag = "tag" in
  let tag_type = tag_type st in
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
(* TODO     (LPred(
	 "eq",
	 [ LConst(Prim_bool true);
	   LApp("select", [LVar mutable_name; LVar this]) ]));*)
      inv;
      components_pre
    ]
  in
  let ensures =
(* TODO    make_and
      (LPred(
	 "eq",
	 [ LVar mutable_name;
	   LApp(
	     "store",
	     [ LVarAtLabel(mutable_name, "");
	       LVar this;
	       LConst(Prim_bool false) ])]))*)
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

let unpack_declaration st acc =
  let this = "this" in
  let this_type = pointer_type st.jc_struct_info_root in
  let tag = "tag" in
  let tag_type = tag_type st in
  let name = st.jc_struct_info_root in
  let mutable_name = mutable_name name in
  let committed_name = committed_name name in
  let reads = StringSet.singleton mutable_name in
  let writes = StringSet.singleton mutable_name in
  let reads = StringSet.add committed_name reads in
  let components_post, reads, writes = make_components_postcond (LVar this) st reads writes false in
  let requires =
    make_and
(*      (LPred(
	 "eq",
	 [ LConst(Prim_bool false);
	   LApp("select", [LVar mutable_name; LVar this]); ]))*)
      (LPred(
	 "eq",
	 [ LVar tag;
	   LApp("select", [LVar mutable_name; LVar this]) ]))
      (LPred(
	 "eq",
	 [ LConst(Prim_bool false);
	   LApp("select", [LVar committed_name; LVar this]) ]))
  in
  let ensures =
(* TODO    make_and
      (LPred(
	 "eq",
	 [ LVar mutable_name;
	   LApp(
	     "store",
	     [ LVarAtLabel(mutable_name, "");
	       LVar this;
	       LConst(Prim_bool true) ])])) *)
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
