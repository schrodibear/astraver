open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Output

(* other modifications for this extension can be found in:
     jc_main.ml
       phase 6
       production phase 5
     jc_interp.ml
       function tr_fun: call to "make_assume_all_assocs"
       function statement
         JCSassign_heap: call to "make_assume_field_assoc"
         JCSunpack
         JCSpack
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
    simple_logic_type f_type;
  ];
}

let pointer_type st_type = {
  logic_type_name = "pointer";
  logic_type_args = [
    simple_logic_type st_type;
  ];
}

(************************************)
(* Checking an invariant definition *)
(************************************)

let rec term this t =
  match t.jc_term_node with
    | JCTconst _ -> ()
    | JCTif (_, _, _) -> assert false (* TODO *)
    | JCTcast (t, ty) -> term this t
    | JCTinstanceof (t, ty) -> term this t
    | JCToffset_min(t,_) 
    | JCToffset_max(t,_) -> term this t
    | JCTold t -> term this t
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
    | JCTshift (t1, t2) -> term this t1; term this t2
    | JCTvar _ -> ()

let rec assertion this p =
  match p.jc_assertion_node with
    | JCAtrue | JCAfalse -> ()
    | JCAif (_, _, _) -> assert false (* TODO *)
    | JCAinstanceof(t,_)
    | JCAbool_term t -> term this t
    | JCAold p -> assertion this p
    | JCAforall (id, p) -> assertion this p
    | JCAapp (id, l) ->
	if FieldSet.is_empty id.jc_logic_info_effects.jc_effect_memories
	then List.iter (term this) l
	else
	  Jc_typing.typing_error p.jc_assertion_loc
	    "this call is not allowed in structure invariant"
    | JCAnot p -> assertion this p
    | JCAiff (p1, p2)
    | JCAimplies (p1, p2) -> assertion this p1; assertion this p2
    | JCAand l | JCAor l -> List.iter (assertion this) l


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
  | JCTTshift(t1, t2) -> term_memories (term_memories aux t1) t2
  | JCTTderef(t, fi) ->
      let m = fi.jc_field_info_name in
      term_memories (StringSet.add m aux) t
  | JCTTapp(_, l) -> List.fold_left term_memories aux l
  | JCTTold t
  | JCTToffset_max(t, _)
  | JCTToffset_min(t, _)
  | JCTTinstanceof(t, _)
  | JCTTcast(t, _) -> term_memories aux t
  | JCTTif(t1, t2, t3) -> term_memories (term_memories (term_memories aux t1) t2) t3

let rec assertion_memories aux a = match a.jc_tassertion_node with
  | JCTAtrue
  | JCTAfalse -> aux
  | JCTAand l
  | JCTAor l -> List.fold_left assertion_memories aux l
  | JCTAimplies(a1, a2)
  | JCTAiff(a1, a2) -> assertion_memories (assertion_memories aux a1) a2
  | JCTAnot a
  | JCTAold a
  | JCTAforall(_, a) -> assertion_memories aux a
  | JCTAapp(_, l) -> List.fold_left term_memories aux l
  | JCTAinstanceof(t, _)
  | JCTAbool_term t -> term_memories aux t
  | JCTAif(t, a1, a2) -> assertion_memories (assertion_memories (term_memories aux t) a1) a2

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

(* Returns the parameters needed by an invariant, "this" not included *)
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
      "", memory_type "'a" "'b" ],
    prop_type)

let make_assoc pp m =
  LPred("assoc", [LConst(Prim_int pp); LVar m])

let make_assoc_list pp mems =
  make_and_list (List.map (make_assoc pp) mems)

let make_assume_assocs pp mems =
  let assocs = make_assoc_list pp mems in
  BlackBox (Annot_type (LTrue, unit_type, mems, [], assocs, []))

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
    ) (StringSet.singleton ("mutable_"^fi.jc_field_info_root)) invs in
  StringSet.elements mems

(* Assume all assocs needed after a field has been modified *)
let make_assume_field_assocs pp fi =
  make_assume_assocs pp (field_assocs fi)

(* Returns a list of all memories which need an "assoc"
(calculated from a function parameter list) *)
let all_assocs pp params =
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
  let structures = StringSet.elements structures in
  (* memories used by these structures' invariants *)
  let memories = List.fold_left
    struct_inv_memories
    StringSet.empty
    structures
  in
  (* mutable fields *)
  let mutable_fields = List.map (fun s -> "mutable_"^s) structures in
  StringSet.elements memories@mutable_fields

(* Assume all assocs needed at the start of a fonction *)
let make_assume_all_assocs pp params =
  make_assume_assocs pp (all_assocs pp params)

(***********)
(* mutable *)
(***********)

let mutable_memory_type struct_name =
  memory_type struct_name "bool"

let mutable_declaration st acc =
  if st.jc_struct_info_parent = None then
    Param(
      false,
      "mutable_"^st.jc_struct_info_name,
      Ref_type(Base_type (memory_type st.jc_struct_info_name "bool"))
    )::acc
  else
    acc

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
  List.fold_left (invariant_axiom st) acc invs

(*****************)
(* pack / unpack *)
(*****************)

let pack_declaration st acc =
  let this = "this" in
  let name = st.jc_struct_info_root in
  let mutable_name = "mutable_"^name in
  let struct_type = pointer_type st.jc_struct_info_root in
  if st.jc_struct_info_parent = None then
    Param(
      false,
      "pack_"^st.jc_struct_info_root,
      Prod_type(
	this,
	Base_type (struct_type),
	Annot_type(
	  LPred(
	    "eq",
	    [ LConst(Prim_bool true);
	      LApp("select", [LVar mutable_name; LVar this]) ]),
	  Base_type (simple_logic_type "unit"),
	  [mutable_name],
	  [mutable_name],
	  LPred(
	    "eq",
	    [ LVar mutable_name;
	      LApp(
		"store",
		[ LVarAtLabel(mutable_name, "");
		  LVar this;
		  LConst(Prim_bool false) ])]),
	  []
	)
      )
    )::acc
  else
    acc

let unpack_declaration st acc =
  let this = "this" in
  let name = st.jc_struct_info_root in
  let mutable_name = "mutable_"^name in
  let struct_type = pointer_type st.jc_struct_info_root in
  if st.jc_struct_info_parent = None then
    Param(
      false,
      "unpack_"^st.jc_struct_info_root,
      Prod_type(
	this,
	Base_type (struct_type),
	Annot_type(
	  LPred(
	    "eq",
	    [ LConst(Prim_bool false);
	      LApp("select", [LVar mutable_name; LVar this]) ]),
	  Base_type (simple_logic_type "unit"),
	  [mutable_name],
	  [mutable_name],
	  LPred(
	    "eq",
	    [ LVar mutable_name;
	      LApp(
		"store",
		[ LVarAtLabel(mutable_name, "");
		  LVar this;
		  LConst(Prim_bool true) ])]),
	  []
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
