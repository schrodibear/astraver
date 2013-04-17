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

(* Import from Cil *)
open Cabs
open Cil_types
open Cil
open Cil_datatype
open Ast_info
open Extlib

open Visitor

(* Utility functions *)
open Common

(*****************************************************************************)
(* Adds a default behavior for all functions                                 *)
(*****************************************************************************)

class add_default_behavior =
  object(self)
    inherit Visitor.frama_c_inplace

    method vspec s =
      if not (List.exists (fun x -> x.b_name = Cil.default_behavior_name)
                s.spec_behavior)
      then begin
        let bhv = Cil.mk_behavior ~name:Cil.default_behavior_name () in
        let kf = Extlib.the self#current_kf in
        let props = Property.ip_all_of_behavior kf Kglobal bhv in
        List.iter Property_status.register props;
        s.spec_behavior <- bhv :: s.spec_behavior
      end;
      SkipChildren

    method vcode_annot _ = SkipChildren

    method vfile _f =
(*
      let init = Globals.Functions.get_glob_init f  in
      Format.eprintf "Rewrite.add_default_behavior#vfile: f = %s@." f.fileName;
      ignore (visitFramacFunspec (self:>Visitor.frama_c_visitor) init.spec);
*)
      DoChildren
  end

let add_default_behavior () =
  let treat_one_function kf =
    let bhvs = Annotations.behaviors kf in
    if not 
      (List.exists (fun bhv -> bhv.b_name = Cil.default_behavior_name) bhvs)
    then begin
      Annotations.add_behaviors Common.jessie_emitter kf [Cil.mk_behavior()];
      (* ensures that default behavior will be correctly populated *)
      ignore (Annotations.behaviors kf)
    end
  in
  Globals.Functions.iter treat_one_function

(*****************************************************************************)
(* Rename entities to avoid conflicts with Jessie predefined names.          *)
(*****************************************************************************)

class renameEntities
  (add_variable : varinfo -> unit) (add_logic_variable : logic_var -> unit) =
  let types = Typ.Hashtbl.create 17 in
  let add_field fi =
    fi.fname <- unique_name fi.fname
  in
  let add_type ty =
    if Typ.Hashtbl.mem types ty then () else
      let compinfo = get_struct_info ty in
      compinfo.cname <- unique_name compinfo.cname;
      List.iter add_field compinfo.cfields;
      Typ.Hashtbl.add types ty ()
  in
object

  inherit Visitor.frama_c_inplace

  method vfunc f =
    List.iter add_variable f.slocals;
    DoChildren

  method vglob_aux = function
    | GCompTag(compinfo,_loc)
    | GCompTagDecl(compinfo,_loc) ->
	add_type (TComp(compinfo,empty_size_cache (),[]));
	SkipChildren
    | GVarDecl _ | GVar _ | GFun _ | GAnnot _ | GType _
    | GEnumTagDecl _ | GEnumTag _ | GAsm _ | GPragma _ | GText _ ->
	DoChildren

  method vlogic_var_decl lv = add_logic_variable lv; DoChildren

  method vlogic_var_use v =
    let postaction v =
      (* Restore consistency between C variable name and logical name *)
      Extlib.may (fun cv -> v.lv_name <- cv.vname) v.lv_origin; v
    in
    ChangeDoChildrenPost(v,postaction)
end

let logic_names_overloading = Hashtbl.create 257

let rename_entities file =
  let add_variable v =
    let s = unique_name v.vname in
(*
    Format.eprintf "Renaming variable %s into %s@." v.vname s;
*)
    v.vname <- s;
    match v.vlogic_var_assoc with
      | None -> ()
      | Some lv -> lv.lv_name <- v.vname
  in
  let add_logic_variable v =
    match v.lv_origin with
        None -> (* pure logic variable *)
          v.lv_name <- unique_logic_name v.lv_name
      | Some _ -> () (* we take care of that in the C world *)
  in
  Globals.Vars.iter (fun v _init -> add_variable v);
  Globals.Functions.iter
    (fun kf ->
       add_variable (Globals.Functions.get_vi kf);
       List.iter add_variable (Globals.Functions.get_params kf));
(* [VP 2011-08-22] replace_all has disappeared from kernel's API, but
   it appears that info in Globals.Annotations is not used by Jessie. *)
(*  Globals.Annotations.replace_all
    (fun annot gen ->
       let rec replace_annot annot = match annot with
	 | Dfun_or_pred _ -> annot
	 | Dvolatile _ -> annot
         | Daxiomatic(id, l, loc) ->
             Daxiomatic(id, List.map replace_annot l,loc)
	 | Dtype(infos,loc) ->
	     Dtype({ infos with
                       lt_name = unique_logic_name infos.lt_name;
                       lt_def =
                       opt_map
                         (function
                              | LTsum cons ->
                                  LTsum(
                                    List.map
                                      (fun x ->
                                         { x with ctor_name =
                                             unique_logic_name x.ctor_name})
                                      cons)
                              | (LTsyn _) as def -> def)
                         infos.lt_def;},
                   loc
                  )
	 | Dlemma(name,is_axiom,labels,poly,property,loc) ->
	     Dlemma(unique_logic_name name,is_axiom,labels,poly,property,loc)
         | Dmodel_annot _ -> annot
	 | Dtype_annot _ | Dinvariant _ ->
	     (* Useful ? harmless ?
		info.l_name <- unique_logic_name info.l_name;
	     *)
	     annot
       in replace_annot annot,gen
    );
*)
  (* preprocess of renaming logic functions  *)
  Logic_env.Logic_info.iter
    (fun name _li ->
       try
	 let x = Hashtbl.find logic_names_overloading name in
	 x := true
       with
	   Not_found ->
	     Hashtbl.add logic_names_overloading name (ref false)
    );

  let visitor = new renameEntities (add_variable) (add_logic_variable) in
  visitFramacFile visitor file


(*****************************************************************************)
(* Fill offset/size information in fields                                    *)
(*****************************************************************************)

class fillOffsetSizeInFields =
object

  inherit Visitor.frama_c_inplace

  method vglob_aux = function
    | GCompTag(compinfo,_loc) ->
	let basety = TComp(compinfo,empty_size_cache () ,[]) in
	let field fi nextoff =
	  let size_in_bits =
	    match fi.fbitfield with
	      | Some siz -> siz
	      | None -> bitsSizeOf fi.ftype
	  in
	  let offset_in_bits = fst (bitsOffset basety (Field(fi,NoOffset))) in
	  let padding_in_bits = nextoff - (offset_in_bits + size_in_bits) in
	  assert (padding_in_bits >= 0);
	  fi.fsize_in_bits <- Some size_in_bits;
	  fi.foffset_in_bits <- Some offset_in_bits;
	  fi.fpadding_in_bits <- Some padding_in_bits;
	  if compinfo.cstruct then
	    offset_in_bits
	  else nextoff (* union type *)
	in
	ignore(List.fold_right field compinfo.cfields (bitsSizeOf basety));
	SkipChildren
    | _ -> SkipChildren

end

let fill_offset_size_in_fields file =
  let visitor = new fillOffsetSizeInFields in
  visitFramacFile visitor file


(*****************************************************************************)
(* Replace addrof array with startof.                                        *)
(*****************************************************************************)

class replaceAddrofArray =
object

  inherit Visitor.frama_c_inplace

  method vexpr e = match e.enode with
    | AddrOf lv ->
	if isArrayType(typeOfLval lv) then
	  ChangeDoChildrenPost (new_exp ~loc:e.eloc (StartOf lv), fun x -> x)
	else DoChildren
    | _ -> DoChildren

  method vterm t = match t.term_node with
    | TAddrOf tlv ->
	let ty = force_app_term_type pointed_type t.term_type in
	if isArrayType ty then
	  let t' = { t with
	    term_node = TStartOf tlv;
	    term_type = Ctype (element_type ty);
	  } in
	  ChangeDoChildrenPost (t', fun x -> x)
	else DoChildren
    | _ -> DoChildren

end

let replace_addrof_array file =
  let visitor = new replaceAddrofArray in
  visit_and_update_globals visitor file


(*****************************************************************************)
(* Replace string constants by global variables.                             *)
(*****************************************************************************)

class replaceStringConstants =

  let string_to_var = Datatype.String.Hashtbl.create 17 in
  let wstring_to_var = Cil_datatype.Wide_string.Hashtbl.create 17 in

  (* Use the Cil translation on initializers. First translate to primitive
   * AST to later apply translation in [blockInitializer].
   *)
  let string_cabs_init s =
    SINGLE_INIT(
      { expr_node = CONSTANT(CONST_STRING s); expr_loc = Cabshelper.cabslu }
    )
  in
  let wstring_cabs_init ws =
    SINGLE_INIT(
      { expr_node = CONSTANT(CONST_WSTRING ws); expr_loc = Cabshelper.cabslu }
    )
  in

  (* Name of variable should be as close as possible to the string it
   * represents. To that end, we just filter out characters not allowed
   * in C names, before we add a discriminating number if necessary.
   *)
  let string_var s =
    let name = unique_name ("__string_" ^ (filter_alphanumeric s [] '_')) in
    makeGlobalVar name (array_type charType)
  in
  let wstring_var () =
    let name = unique_name "__wstring_" in
    makeGlobalVar name (array_type theMachine.wcharType)
(*     makeGlobalVar name (array_type (TInt(IUShort,[]))) *)
  in

  let make_glob ~wstring v size inite =
    (* Apply translation from initializer in primitive AST to block of code,
     * simple initializer and type.
     *)
    let _b,init,ty =
      Cabs2cil.blockInitializer Cabs2cil.empty_local_env v inite in
    (* Precise the array type *)
    v.vtype <- ty;
    (* Attach global variable and code for global initialization *)
(* DISABLED because does not work and uses deprecated Cil.getGlobInit
   See bts0284.c
    List.iter attach_globinit b.bstmts;
*)
    attach_global (GVar(v,{init=Some init},CurrentLoc.get ()));
    (* Define a global string invariant *)
    begin try
    let validstring =
      match Logic_env.find_all_logic_functions
	(if wstring then
	   name_of_valid_wstring
	 else
	   name_of_valid_string)
      with
	| [i] -> i
	| _  -> raise Exit
    in
    let strlen =
      match Logic_env.find_all_logic_functions name_of_strlen
      with
	| [i] -> i
	| _  -> raise Exit
    in
    let strlen_type =
      match strlen.l_type with Some t -> t | None -> assert false
    in
    let wcslen =
      match Logic_env.find_all_logic_functions name_of_wcslen
      with
	| [i] -> i
	| _  -> raise Exit
    in
    let wcslen_type =
      match wcslen.l_type with Some t -> t | None -> assert false
    in
    let pstring =
      Papp(validstring,[],[variable_term v.vdecl (cvar_to_lvar v)])
    in
    let tv = term_of_var v in
    let strsize =
      if wstring then
	mkterm (Tapp(wcslen,[],[tv])) wcslen_type v.vdecl
      else
	mkterm (Tapp(strlen,[],[tv])) strlen_type v.vdecl
    in
    let size = constant_term v.vdecl (Integer.of_int size) in
    let psize = Prel(Req,strsize,size) in
    let p = Pand(predicate v.vdecl pstring,predicate v.vdecl psize) in
    let globinv =
      Cil_const.make_logic_info (unique_logic_name ("valid_" ^ v.vname)) in
    globinv.l_labels <- [ LogicLabel (None, "Here") ];
    globinv.l_body <- LBpred (predicate v.vdecl p);
    attach_globaction (fun () -> Logic_utils.add_logic_function globinv);
    attach_global (GAnnot(Dinvariant (globinv,v.vdecl),v.vdecl));
    with Exit -> ()
    end;
    v
  in
object

  inherit Visitor.frama_c_inplace

  method vexpr e = match e.enode with
    | Const(CStr s) ->
	let v =
	  Datatype.String.Hashtbl.memo string_to_var s
	    (fun s ->
	       make_glob ~wstring:false (string_var s) (String.length s)
		 (string_cabs_init s))
	in
	ChangeTo (new_exp ~loc:e.eloc (StartOf(Var v,NoOffset)))
    | Const(CWStr ws) ->
	let v =
	  Cil_datatype.Wide_string.Hashtbl.memo wstring_to_var ws
	    (fun ws ->
	       make_glob ~wstring:true (wstring_var ()) (List.length ws - 1)
		 (wstring_cabs_init ws))
	in
	ChangeTo (new_exp ~loc:e.eloc (StartOf(Var v,NoOffset)))
    | _ -> DoChildren

  method vglob_aux = function
    | GVar(v,{init=Some(SingleInit({enode = Const _}))},_) ->
	if isArrayType v.vtype then
	  (* Avoid creating an array for holding the initializer for another
	   * array. This initializer is later cut into individual
	   * initialization statements in [gather_initialization].
	   *)
	  SkipChildren
	else
	  DoChildren
    | _ -> DoChildren

end

let replace_string_constants file =
  let visitor = new replaceStringConstants in
  visit_and_update_globals visitor file


(*****************************************************************************)
(* Put all global initializations in the [globinit] file.                    *)
(* Replace global compound initializations by equivalent statements.         *)
(*****************************************************************************)

let gather_initialization file =
  do_and_update_globals
    (fun _ ->
      Globals.Vars.iter (fun v iinfo ->
	let _s = match iinfo.init with
	  | Some ie ->
	      let b =
                Cabs2cil.blockInit
                  ~ghost:v.vghost (Var v, NoOffset) ie v.vtype in
	      b.bstmts
	  | None ->
	      if bitsSizeOf v.vtype lsr 3 < 100 then
		(* Enforce zero-initialization of global variables *)
		let ie = 
                  makeZeroInit ~loc:Cil_datatype.Location.unknown v.vtype 
                in
		let b =
                  Cabs2cil.blockInit
                    ~ghost:v.vghost (Var v, NoOffset) ie v.vtype
                in
		b.bstmts
	      else
		(* FS#253: Big data structure, do not initialize individually.
		 * When casts to low-level are supported, call here [memset]
		 * or equivalent to zero the memory.
		 *)
		[]
	in
	(* Too big currently, postpone until useful *)
(*
	ignore s;
  	List.iter attach_globinit s;
*)
	iinfo.init <- None
      )) file

class copy_spec_specialize_memset =
object(self)
  inherit Visitor.frama_c_copy (Project.current())
  method private has_changed lv =
    (Cil.get_original_logic_var self#behavior lv) != lv

  method vlogic_var_use lv =
    if self#has_changed lv then DoChildren (* Already visited *)
    else begin
      match lv.lv_origin with
        | Some v when not v.vglob -> (* Don't change global references *)
            let v' = Cil_const.copy_with_new_vid v in
            v'.vformal <- true;
            (match Cil.unrollType v.vtype with
              | TArray _ as t -> v'.vtype <- TPtr(t,[])
              | _ -> ());
            v'.vlogic_var_assoc <- None; (* reset association. *)
            let lv' = Cil.cvar_to_lvar v' in
            Cil.set_logic_var self#behavior lv lv';
            Cil.set_orig_logic_var self#behavior lv' lv;
            Cil.set_varinfo self#behavior v v';
            Cil.set_orig_varinfo self#behavior v' v;
            ChangeTo lv'
        | Some _ | None -> DoChildren
    end

  method vterm t =
    let post_action t =
      let loc = t.term_loc in
      match t.term_node with
        | TStartOf (TVar lv, TNoOffset) ->
            if self#has_changed lv then begin
              (* Original was an array, and is now a pointer to an array.
                 Update term accordingly*)
              let base = Logic_const.tvar ~loc lv in
              let tmem = (TMem base,TNoOffset) in
              Logic_const.term
                ~loc (TStartOf tmem) (Cil.typeOfTermLval tmem)
            end else t
        | TLval (TVar lv, (TIndex _ as idx)) ->
            if self#has_changed lv then begin
                (* Change array access into pointer shift. *)
              let base = Logic_const.tvar ~loc lv in
              let tmem = TMem base, idx in
              Logic_const.term ~loc (TLval tmem) t.term_type
            end else t
        | _ -> t
    in ChangeDoChildrenPost(t,post_action)

  method vspec s =
    let refresh_deps = function
      | FromAny -> FromAny
      | From locs -> From (List.map Logic_const.refresh_identified_term locs)
    in
    let refresh_froms (loc,deps) =
      (Logic_const.refresh_identified_term loc, refresh_deps deps)
    in
    let refresh_assigns = function
      | WritesAny -> WritesAny
      | Writes (writes) -> Writes (List.map refresh_froms writes)
    in
    let refresh_allocates = function
      | FreeAllocAny -> FreeAllocAny
      | FreeAlloc (free,alloc) ->
          FreeAlloc (List.map Logic_const.refresh_identified_term free,
                     List.map Logic_const.refresh_identified_term alloc)
    in
    let refresh_extended e =
      List.map (fun (s,i,p) -> (s,i,List.map Logic_const.refresh_predicate p)) e
    in
    let refresh_behavior b =
      let requires = List.map Logic_const.refresh_predicate b.b_requires in
      let assumes = List.map Logic_const.refresh_predicate b.b_assumes in
      let post_cond = 
        List.map
          (fun (k,p) -> (k,Logic_const.refresh_predicate p)) b.b_post_cond
      in
      let assigns = refresh_assigns b.b_assigns in
      let allocation = Some (refresh_allocates b.b_allocation) in
      let extended = refresh_extended b.b_extended in
      Cil.mk_behavior
        ~assumes ~requires ~post_cond ~assigns ~allocation ~extended ()
    in
    let refresh s =
      let bhvs = List.map refresh_behavior s.spec_behavior in
      s.spec_behavior <- bhvs;
      s
    in
    ChangeDoChildrenPost(s,refresh)
end

let copy_spec_specialize_memset s =
  let vis = new copy_spec_specialize_memset in
  let s' = Visitor.visitFramacFunspec vis s in
  let args =
    Cil.fold_visitor_varinfo 
      vis#behavior (fun oldv newv acc -> (oldv,newv)::acc) []
  in
  args,s'

class specialize_memset =
object
  inherit Visitor.frama_c_inplace
  val mutable my_globals = []
  method vstmt_aux s =
    match Annotations.code_annot ~filter:Logic_utils.is_contract s with
      | [ annot ] ->
          (match annot.annot_content with
             | AStmtSpec
                (_,({ spec_behavior =
                    [ { b_name = "Frama_C_implicit_init" }]} as spec))
              ->
                let loc = Cil_datatype.Stmt.loc s in
                let mk_actual v =
                  match Cil.unrollType v.vtype with
                    | TArray _ ->
                        Cil.new_exp ~loc (StartOf (Cil.var v))
                    | _ -> Cil.evar ~loc v
                in
                let prms, spec = copy_spec_specialize_memset spec in
                let (actuals,formals) = List.split prms in
                let actuals = List.map mk_actual actuals in
                let arg_type =
                  List.map (fun v -> v.vname, v.vtype, []) formals in
                let f =
                  Cil.makeGlobalVar
                    (Common.unique_name "implicit_init")
                    (TFun (TVoid [], Some arg_type, false, []))
                in
                 Cil.unsafeSetFormalsDecl f formals;
                my_globals <- 
                  GVarDecl(Cil.empty_funspec(),f,loc) :: my_globals;
                Globals.Functions.replace_by_declaration spec f loc;
                let kf = Globals.Functions.get f in
                Annotations.register_funspec ~emitter:Common.jessie_emitter kf;
                let my_instr = Call(None,Cil.evar ~loc f,actuals,loc) in
                s.skind <- Instr my_instr;
                SkipChildren
            | _ -> DoChildren)
      | _ -> DoChildren

  method vglob_aux _ =
    let add_specialized g = let s = my_globals in my_globals <- []; s @ g in
    DoChildrenPost add_specialized
end

let specialize_memset file = 
  visitFramacFile (new specialize_memset) file;
  (* We may have introduced new globals: clear the last_decl table. *)
  Ast.clear_last_decl () 

(*****************************************************************************)
(* Rewrite comparison of pointers into difference of pointers.               *)
(*****************************************************************************)

class rewritePointerCompare =
  let preaction_expr e = match e.enode with
    | BinOp((Lt | Gt | Le | Ge | Eq | Ne as op),e1,e2,ty)
	when isPointerType (typeOf e1) && not (is_null_expr e2) ->
	new_exp ~loc:e.eloc
          (BinOp(op,
                 new_exp ~loc:e.eloc
                   (BinOp(MinusPP,e1,e2,theMachine.ptrdiffType)),
	         constant_expr Integer.zero,ty))
    | _ -> e
  in
object

  inherit Visitor.frama_c_inplace

  method vexpr e =
    ChangeDoChildrenPost (preaction_expr e, fun x -> x)

  method vterm =
    do_on_term (Some preaction_expr,None)

  method vpredicate = function
    | Prel(rel,t1,t2)
	when app_term_type isPointerType false t1.term_type
	  && not (is_null_term t1 || is_null_term t2
		  || is_base_addr t1 || is_base_addr t2) ->
	let loc = range_loc t1.term_loc t2.term_loc in
	let tsub = {
	  term_node = TBinOp(MinusPP,t1,t2);
	  term_type = Ctype theMachine.ptrdiffType;
	  term_loc = loc;
	  term_name = [];
	} in
	let p = Prel(rel,tsub,constant_term loc Integer.zero) in
	ChangeDoChildrenPost (p, fun x -> x)
    | _ -> DoChildren

end

let rewrite_pointer_compare file =
  let visitor = new rewritePointerCompare in
  visitFramacFile visitor file


(*****************************************************************************)
(* Rewrite cursor pointers into offsets from base pointers.                  *)
(*****************************************************************************)

(* Recognize the sum of a pointer variable and an integer offset *)
let rec destruct_pointer e = match (stripInfo e).enode with
  | Lval(Var v,NoOffset) | StartOf(Var v,NoOffset) | AddrOf(Var v,NoOffset) ->
      Some(v,None)
  | StartOf(Var v,Index(i,NoOffset)) | AddrOf(Var v,Index(i,NoOffset)) ->
      Some(v,Some i)
  | BinOp((PlusPI | IndexPI | MinusPI as op),e1,e2,_) ->
      begin match destruct_pointer e1 with
	| None -> None
	| Some(v,None) ->
	    begin match op with
	      | PlusPI | IndexPI -> Some(v,Some e2)
	      | MinusPI ->
                  Some(v,
                       Some(new_exp ~loc:e.eloc (UnOp(Neg,e2,typeOf e2))))
	      | _ -> assert false
	    end
	| Some(v,Some off) ->
	    begin match op with
	      | PlusPI | IndexPI ->
                  Some(v,
                       Some(new_exp ~loc:e.eloc
                              (BinOp(PlusA,off,e2,typeOf e2))))
	      | MinusPI ->
                  Some(v,
                       Some(new_exp ~loc:e.eloc
                              (BinOp(MinusA,off,e2,typeOf e2))))
	      | _ -> assert false
	    end
      end
  | CastE(ty,e) ->
      let ety = typeOf e in
      if isPointerType ty && isPointerType ety
	&&
          Cil_datatype.Typ.equal
          (Cil.typeDeepDropAttributes ["const"; "volatile"]
             (unrollType (pointed_type ty)))
          (Cil.typeDeepDropAttributes ["const"; "volatile"]
             (unrollType (pointed_type ety)))
      then
	destruct_pointer e
      else None
  | _ -> None

class collectCursorPointers
  (cursor_to_base : varinfo Cil_datatype.Varinfo.Hashtbl.t) (* local variable to base *)
  (formal_to_base : varinfo Cil_datatype.Varinfo.Hashtbl.t) (* formal variable to base *)
  (assigned_vars : Cil_datatype.Varinfo.Set.t ref) (* variable is assigned (for formals) *)
  (ignore_vars : Cil_datatype.Varinfo.Set.t ref) (* ignore info on these variables *) =

  let curFundec : fundec ref = ref (emptyFunction "@dummy@") in

  let candidate_var v =
    not v.vglob
    && ((isPointerType v.vtype && not v.vaddrof) || isArrayType v.vtype)
  in
  (* Variable should not be translated as base or cursor *)
  let add_ignore_vars v =
    if not (Cil_datatype.Varinfo.Set.mem v !ignore_vars) then
      begin
	ignore_vars := Cil_datatype.Varinfo.Set.add v !ignore_vars; signal_change ()
      end
  in
  (* Variable [v] used as cursor on base [vb] *)
  let add_cursor_to_base v vb =
    try
      let vb2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
      if not (Cil_datatype.Varinfo.equal vb vb2) then add_ignore_vars v
    with Not_found ->
      Cil_datatype.Varinfo.Hashtbl.add cursor_to_base v vb; signal_change ()
  in
  (* Variable [v] assigned *)
  let add_assigned_vars v =
    if not (Cil_datatype.Varinfo.Set.mem v !assigned_vars) then
      begin
	assigned_vars := Cil_datatype.Varinfo.Set.add v !assigned_vars; signal_change ()
      end
  in

  (* Interpret difference of pointers as a hint that one is an cursor
   * of the other. *)
  let preaction_expr x =
    begin match x.enode with
      | BinOp(MinusPP,e1,e2,_) when isPointerType (typeOf e1) ->
	  begin match destruct_pointer e1,destruct_pointer e2 with
	    | Some(v1,_),Some(v2,_) ->
		begin try
		  let vb1 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v1 in
		  let vb2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v2 in
		  if not (Cil_datatype.Varinfo.equal vb1 vb2)
		    && vb1.vformal && vb2.vformal then
		      (* One formal is an offset from the other.
			 Choose the first one in the list of parameters
			 as base. *)
		      let vbbase,vboff =
			match
			  List.fold_left
			    (fun acc v ->
			       match acc with Some _ -> acc | None ->
		      		 if Cil_datatype.Varinfo.equal v vb1 then
				   Some(vb1,vb2)
				 else if Cil_datatype.Varinfo.equal v vb2 then
				   Some(vb2,vb1)
				 else None
			    ) None !curFundec.sformals
			with None -> assert false | Some pair -> pair
		      in
		      Cil_datatype.Varinfo.Hashtbl.add formal_to_base vboff vbbase
		  else ()
		with Not_found -> () end
	    | _ -> ()
	  end
      | _ -> ()
    end; x
  in
object

  inherit Visitor.frama_c_inplace

  method vfunc f =
    curFundec := f;
    (* For simplicity, consider formals as self-cursors initially.
     * This is the way we declare bases (in the image of [cursor_to_base]).
     *)
    let formal v =
      if candidate_var v then add_cursor_to_base v v
    in
    let local v =
      (* Consider local arrays as candidate base pointers *)
      if isArrayType v.vtype then formal v
    in
    List.iter formal f.sformals;
    List.iter local f.slocals;
    DoChildren

  method vinst = function
    | Set((Var v,NoOffset),e,_loc) ->
	if candidate_var v then
	  begin
	    add_assigned_vars v;
	    match destruct_pointer e with
	      | None -> add_ignore_vars v
	      | Some(v2,_offset) ->
		  if Cil_datatype.Varinfo.Set.mem v2 !ignore_vars then add_ignore_vars v
		  else try
		    let vb2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v2 in
		    try
		      let vb = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
		      if not (Cil_datatype.Varinfo.equal vb vb2) then
			add_ignore_vars v
		    with Not_found -> add_cursor_to_base v vb2
		  with Not_found -> add_ignore_vars v
	  end;
	DoChildren
    | Set _ -> DoChildren
    | Call(Some(Var v,NoOffset),_f,_args,_loc) ->
	if candidate_var v then
	  begin
	    add_assigned_vars v; add_ignore_vars v
	  end;
	DoChildren
    | Call _ -> DoChildren
    | Asm _ | Skip _ -> SkipChildren
    | Code_annot _ -> assert false

  method vexpr e =
    ignore(preaction_expr e); DoChildren

  method vterm = do_on_term (Some preaction_expr, None)

end

class rewriteCursorPointers
  (cursor_to_base : varinfo Cil_datatype.Varinfo.Hashtbl.t)
  (formal_to_base : varinfo Cil_datatype.Varinfo.Hashtbl.t)
  (assigned_vars : Cil_datatype.Varinfo.Set.t) =

  (* Correspondance between cursor variables and offset variables *)
  let cursor_to_offset : varinfo Cil_datatype.Varinfo.Hashtbl.t = Cil_datatype.Varinfo.Hashtbl.create 0 in

  (* Function [expr_offset] may raise exception [Not_found] if
   * no offset needed.
   *)
  let expr_offset v =
    let loc = Cil_const.CurrentLoc.get () in
    if v.vformal then
      let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
      new_exp ~loc (Lval(Var voff,NoOffset))
    else
      let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
      let vb = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
      if Cil_datatype.Varinfo.Hashtbl.mem formal_to_base vb then
	let voff2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset vb in
	new_exp ~loc
          (BinOp(PlusA,
                 new_exp ~loc (Lval(Var voff,NoOffset)),
                 new_exp ~loc (Lval(Var voff2,NoOffset)),
	         theMachine.ptrdiffType))
      else new_exp ~loc (Lval(Var voff,NoOffset))
  in
  (* Find basis for variable [v] *)
  let var_base v =
    if Cil_datatype.Varinfo.Hashtbl.mem cursor_to_offset v then
      if v.vformal then
	try Cil_datatype.Varinfo.Hashtbl.find formal_to_base v
	with Not_found -> v (* self-base *)
      else
	let vb = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
	try Cil_datatype.Varinfo.Hashtbl.find formal_to_base vb
	with Not_found -> vb
    else
      raise Not_found
  in
  let lval_base vb =
    let loc = Cil_const.CurrentLoc.get () in
    if isArrayType vb.vtype then
      new_exp ~loc (StartOf(Var vb,NoOffset))
    else
      new_exp ~loc (Lval(Var vb,NoOffset))
  in
  let preaction_expr e = match e.enode with
    | BinOp(MinusPP,e1,e2,_) ->
        begin try match destruct_pointer e1,destruct_pointer e2 with
          | None,_ | _,None -> e
          | Some(v1,offopt1),Some(v2,offopt2) ->
	      let vb1 = try var_base v1 with Not_found -> v1 in
	      let vb2 = try var_base v2 with Not_found -> v2 in
              if Cil_datatype.Varinfo.equal vb1 vb2 then
	        let v1offopt =
		  try Some(expr_offset v1) with Not_found -> None in
	        let v2offopt =
		  try Some(expr_offset v2) with Not_found -> None in
                let offopt1 = match v1offopt,offopt1 with
                  | None,None -> None
                  | Some off,None | None,Some off -> Some off
                  | Some off1,Some off2 ->
                      Some
                        (new_exp ~loc:e.eloc
                           (BinOp(PlusA,off1,off2,theMachine.ptrdiffType)))
                in
                let offopt2 = match v2offopt,offopt2 with
                  | None,None -> None
                  | Some off,None | None,Some off -> Some off
                  | Some off1,Some off2 ->
                      Some
                        (new_exp ~loc:e.eloc
                           (BinOp(PlusA,off1,off2,theMachine.ptrdiffType)))
                in
                match offopt1,offopt2 with
                  | Some off1,Some off2 ->
		      new_exp ~loc:e.eloc
                        (BinOp(MinusA,off1,off2,theMachine.ptrdiffType))
                  | Some off1,None ->
		      off1
                  | None,Some off2 ->
	              new_exp ~loc:e.eloc
                        (UnOp(Neg,off2,theMachine.ptrdiffType))
                  | None,None ->
		      constant_expr Integer.zero
              else e
	with Not_found -> e end
    | _ -> e
  in
  let postaction_expr e = match e.enode with
    | Lval(Var v,NoOffset) ->
	begin try
	  (* Both [var_base] and [expr_offset] can raise [Not_found],
	   * the second one only on local array variables.
	   *)
	  let vb = var_base v in
	  new_exp ~loc:e.eloc
            (BinOp(PlusPI,lval_base vb,expr_offset v,v.vtype))
	with Not_found -> e end
    | _ -> e
  in
object

  inherit Visitor.frama_c_inplace

  method vfunc f =
    let local v =
      if Cil_datatype.Varinfo.Hashtbl.mem cursor_to_base v && not (isArrayType v.vtype) then
	let name = unique_name ("__jc_off_" ^ v.vname) in
	let voff = makeLocalVar f ~insert:true name almost_integer_type in
	Cil_datatype.Varinfo.Hashtbl.add cursor_to_offset v voff
    in
    let formal v =
      if Cil_datatype.Varinfo.Hashtbl.mem formal_to_base v then
	(* Formal is a cursor of another formal *)
	begin
	  local v; (* Create an offset variable for this formal *)
	  let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	  let vb = Cil_datatype.Varinfo.Hashtbl.find formal_to_base v in
          let loc = CurrentLoc.get () in
	  let initst =
	    mkStmt(
	      Instr(
                Set((Var voff,NoOffset),
	            new_exp ~loc:(CurrentLoc.get())
                      (BinOp (MinusPP,
                              new_exp ~loc (Lval(Var v,NoOffset)),
                              lval_base vb,
		              theMachine.ptrdiffType)),
		    loc)))
	  in
	  add_pending_statement ~beginning:true initst
	end
      else if Cil_datatype.Varinfo.Hashtbl.mem cursor_to_base v
	&& Cil_datatype.Varinfo.Set.mem v assigned_vars then
	(* Formal is assigned and still a self-base, an offset is needed *)
	begin
	  local v; (* Create an offset variable for this formal *)
	  let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	  let initst =
	    mkStmt(Instr(Set((Var voff,NoOffset),
			     constant_expr Integer.zero,
			     CurrentLoc.get ())))
	  in
	  add_pending_statement ~beginning:true initst
	end
      else ()
    in
    List.iter formal f.sformals;
    List.iter local f.slocals;
    DoChildren

  method vinst = function
    | Set((Var v,NoOffset),e,loc) ->
	if v.vformal then
	  begin try
	    let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	    (* At this point, [e] must be a pointer whose destruction through
	     * [destruct_pointer] does not return None.
	     *)
	    let eoff = match destruct_pointer e with
	      | None -> assert false
	      | Some(v2,Some e) ->
		  begin try
                    new_exp ~loc:e.eloc
                      (BinOp(PlusA,expr_offset v2,e,almost_integer_type))
		  with Not_found -> assert false end
	      | Some(v2,None) ->
		  begin try expr_offset v2
		  with Not_found -> assert false end
	    in
	    ChangeDoChildrenPost
	      ([Set((Var voff,NoOffset),eoff,loc)], fun x -> x)
	  with Not_found -> DoChildren end
	else
	  (* local variable *)
	  begin try
	    let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	    (* At this point, [e] must be a pointer whose destruction through
	     * [destruct_pointer] does not return None.
	     *)
	    let eoff = match destruct_pointer e with
	      | None -> assert false
	      | Some(v2,Some e) ->
		  begin try
                    new_exp ~loc:e.eloc
                      (BinOp(PlusA,expr_offset v2,e,almost_integer_type))
		  with Not_found -> e end
	      | Some(v2,None) ->
		  begin try expr_offset v2
		  with Not_found -> constant_expr Integer.zero end
	    in
	    ChangeDoChildrenPost
	      ([Set((Var voff,NoOffset),eoff,loc)], fun x -> x)
	  with Not_found -> DoChildren end
    | _ -> DoChildren

  method vexpr e =
    ChangeDoChildrenPost (preaction_expr e, postaction_expr)

  method vterm =
    do_on_term (Some preaction_expr,Some postaction_expr)

  method vspec _sp =
    (* Do not modify the function contract, where offset variables
     * are not known *)
    SkipChildren

end

let rewrite_cursor_pointers file =
  (* Variables to communicate between the collecting visitor and
   * the rewriting one. *)
  let cursor_to_base = Cil_datatype.Varinfo.Hashtbl.create 0 in
  let formal_to_base = Cil_datatype.Varinfo.Hashtbl.create 0 in
  let assigned_vars = ref Cil_datatype.Varinfo.Set.empty in
  let ignore_vars = ref Cil_datatype.Varinfo.Set.empty in

  (* Collect the cursor variables and their base *)
  let visitor =
    new collectCursorPointers
      cursor_to_base formal_to_base assigned_vars ignore_vars
  in
  visit_until_convergence visitor file;

  (* Normalize the information *)
  let rec transitive_basis v =
    try transitive_basis (Cil_datatype.Varinfo.Hashtbl.find formal_to_base v)
    with Not_found -> v
  in
  Cil_datatype.Varinfo.Hashtbl.iter
    (fun v _ -> Cil_datatype.Varinfo.Hashtbl.add formal_to_base v (transitive_basis v))
    formal_to_base;
  Cil_datatype.Varinfo.Set.iter
    (fun v -> Cil_datatype.Varinfo.Hashtbl.remove cursor_to_base v) !ignore_vars;
  Cil_datatype.Varinfo.Hashtbl.iter
    (fun v vb -> if Cil_datatype.Varinfo.Set.mem vb !ignore_vars then
      Cil_datatype.Varinfo.Hashtbl.remove cursor_to_base v) cursor_to_base;
  Cil_datatype.Varinfo.Hashtbl.iter
    (fun v vb -> if Cil_datatype.Varinfo.Set.mem vb !ignore_vars then
      Cil_datatype.Varinfo.Hashtbl.remove formal_to_base v) formal_to_base;

  (* Rewrite cursor variables as offsets from their base variable *)
  let visitor =
    new rewriteCursorPointers
      cursor_to_base formal_to_base !assigned_vars
  in
  visitFramacFile (visit_and_push_statements_visitor visitor) file


(*****************************************************************************)
(* Rewrite cursor integers into offsets from base integers.                  *)
(*****************************************************************************)

(* Recognize the sum of an integer variable and an integer offset *)
let rec destruct_integer e = match e.enode with
  | Lval(Var v,NoOffset) -> Some(v,None)
  | BinOp((PlusA | MinusA as op),e1,e2,_) ->
      begin match destruct_integer e1 with
	| None -> None
	| Some(v,None) ->
	    begin match op with
	      | PlusA -> Some(v,Some e2)
	      | MinusA ->
                  Some(v,
                       Some(new_exp ~loc:e.eloc
                              (UnOp(Neg,e2,almost_integer_type))))
	      | _ -> assert false
	    end
	| Some(v,Some off) ->
	    begin match op with
	      | PlusA ->
                  Some(v,
                       Some(new_exp ~loc:e.eloc
                              (BinOp(PlusA,off,e2,almost_integer_type))))
	      | MinusA ->
                  Some(v,
                       Some(new_exp ~loc:e.eloc
                              (BinOp(MinusA,off,e2,almost_integer_type))))
	      | _ -> assert false
	    end
      end
  | CastE(ty,e) ->
      let ety = typeOf e in
      if isIntegralType ty && isIntegralType ety then
	destruct_integer e
      else None
  | _ -> None

class collectCursorIntegers
  (cursor_to_base : varinfo Cil_datatype.Varinfo.Hashtbl.t) (* local variable to base *)
  (assigned_vars : Cil_datatype.Varinfo.Set.t ref) (* variable is assigned (for formals) *)
  (ignore_vars : Cil_datatype.Varinfo.Set.t ref) (* ignore info on these variables *) =

  let candidate_var v =
    not v.vglob && (isIntegralType v.vtype && not v.vaddrof)
  in
  (* Variable should not be translated as base or cursor *)
  let add_ignore_vars v =
    if not (Cil_datatype.Varinfo.Set.mem v !ignore_vars) then
      begin
	ignore_vars := Cil_datatype.Varinfo.Set.add v !ignore_vars; signal_change ()
      end
  in
  (* Variable [v] used as cursor on base [vb] *)
  let add_cursor_to_base v vb =
    try
      let vb2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
      if not (Cil_datatype.Varinfo.equal vb vb2) then add_ignore_vars v
    with Not_found ->
      Cil_datatype.Varinfo.Hashtbl.add cursor_to_base v vb; signal_change ()
  in
  (* Variable [v] assigned *)
  let add_assigned_vars v =
    if not (Cil_datatype.Varinfo.Set.mem v !assigned_vars) then
      begin
	assigned_vars := Cil_datatype.Varinfo.Set.add v !assigned_vars; signal_change ()
      end
  in
object

  inherit Visitor.frama_c_inplace

  method vfunc f =
    (* For simplicity, consider formals as self-cursors initially.
     * This is the way we declare bases (in the image of [cursor_to_base]).
     *)
    let formal v =
      if candidate_var v then add_cursor_to_base v v
    in
    List.iter formal f.sformals;
    DoChildren

  method vinst = function
    | Set((Var v,NoOffset),e,_loc) ->
	if candidate_var v then
	  begin
	    add_assigned_vars v;
	    match destruct_integer e with
	      | None -> add_ignore_vars v
	      | Some(v2,_offset) ->
		  if Cil_datatype.Varinfo.Set.mem v2 !ignore_vars then add_ignore_vars v
		  else try
		    let vb2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v2 in
		    try
		      let vb = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
		      if not (Cil_datatype.Varinfo.equal vb vb2) then
			add_ignore_vars v
		    with Not_found -> add_cursor_to_base v vb2
		  with Not_found -> add_ignore_vars v
	  end;
	SkipChildren
    | Set _ -> SkipChildren
    | Call(Some(Var v,NoOffset),_f,_args,_loc) ->
	if candidate_var v then
	  begin
	    add_assigned_vars v; add_ignore_vars v
	  end;
	SkipChildren
    | Call _ -> SkipChildren
    | Asm _ | Skip _ -> SkipChildren
    | Code_annot _ -> assert false

end

class rewriteCursorIntegers
  (cursor_to_base : varinfo Cil_datatype.Varinfo.Hashtbl.t)
  (assigned_vars : Cil_datatype.Varinfo.Set.t) =

  (* Correspondance between cursor variables and offset variables *)
  let cursor_to_offset : varinfo Cil_datatype.Varinfo.Hashtbl.t = Cil_datatype.Varinfo.Hashtbl.create 0 in

  let postaction_expr e = match e.enode with
    | Lval(Var v,NoOffset) ->
	begin try
	  let vb = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
	  let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	  new_exp ~loc:e.eloc
            (BinOp(PlusA,
                   new_exp ~loc:e.eloc (Lval(Var vb,NoOffset)),
                   new_exp ~loc:e.eloc (Lval(Var voff,NoOffset)),
                   v.vtype))
	with Not_found -> e end
    | _ -> e
  in
  let postaction_term t = match t.term_node with
    | TLval(TVar { lv_origin = Some v },TNoOffset) ->
	begin try
	  let vb = Cil_datatype.Varinfo.Hashtbl.find cursor_to_base v in
	  let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	  let vt1 = term_of_var vb in
	  let vt2 = term_of_var voff in
	  let addt =
	    mkterm (TBinOp(PlusA,vt1,vt2)) Linteger t.term_loc
	  in
	  mkterm (TCastE(v.vtype,addt)) t.term_type t.term_loc
	with Not_found -> t end
    | _ -> t
  in
object

  inherit Visitor.frama_c_inplace

  method vfunc f =
    let local v =
      if Cil_datatype.Varinfo.Hashtbl.mem cursor_to_base v then
	let name = unique_name ("__jc_off_" ^ v.vname) in
	let voff = makeLocalVar f ~insert:true name almost_integer_type in
	Cil_datatype.Varinfo.Hashtbl.add cursor_to_offset v voff
    in
    let formal v =
      if Cil_datatype.Varinfo.Hashtbl.mem cursor_to_base v
	&& Cil_datatype.Varinfo.Set.mem v assigned_vars then
	  (* Formal is assigned and still a self-base, an offset is needed *)
	  begin
	  local v; (* Create an offset variable for this formal *)
	  let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	  let initst =
	    mkStmt(Instr(Set((Var voff,NoOffset),
			     constant_expr Integer.zero,
			     CurrentLoc.get ())))
	  in
	  add_pending_statement ~beginning:true initst
	  end
      else ()
    in
    List.iter formal f.sformals;
    List.iter local f.slocals;
    DoChildren

  method vinst = function
    | Set((Var v,NoOffset),e,loc) ->
	begin try
	  let voff = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v in
	  (* At this point, [e] must be an integer whose destruction through
	   * [destruct_integer] does not return None.
	   *)
	  let eoff = match destruct_integer e with
	    | None -> assert false
	    | Some(v2,Some e) ->
		begin try
		  let voff2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v2 in
		  new_exp ~loc:e.eloc
                    (BinOp(PlusA,
                           new_exp ~loc:e.eloc (Lval(Var voff2,NoOffset)),
                           e,
                           almost_integer_type))
		with Not_found -> e end
	    | Some(v2,None) ->
		begin try
		  let voff2 = Cil_datatype.Varinfo.Hashtbl.find cursor_to_offset v2 in
		  new_exp ~loc (Lval(Var voff2,NoOffset))
		with Not_found -> constant_expr Integer.zero end
	  in
	  ChangeDoChildrenPost
	    ([Set((Var voff,NoOffset),eoff,loc)], fun x -> x)
	with Not_found -> DoChildren end
    | _ -> DoChildren

  method vexpr e =
    ChangeDoChildrenPost (e,postaction_expr)

  method vterm t =
    ChangeDoChildrenPost (t,postaction_term)

  method vspec _sp =
    (* Do not modify the function contract, where offset variables
     * are not known *)
    SkipChildren

end

let rewrite_cursor_integers file =
  (* Variables to communicate between the collecting visitor and
   * the rewriting one. *)
  let cursor_to_base = Cil_datatype.Varinfo.Hashtbl.create 0 in
  let assigned_vars = ref Cil_datatype.Varinfo.Set.empty in
  let ignore_vars = ref Cil_datatype.Varinfo.Set.empty in

  (* Collect the cursor variables and their base *)
  let visitor =
    new collectCursorIntegers
      cursor_to_base assigned_vars ignore_vars
  in
  visit_until_convergence visitor file;

  (* Normalize the information *)
  Cil_datatype.Varinfo.Set.iter
    (fun v -> Cil_datatype.Varinfo.Hashtbl.remove cursor_to_base v) !ignore_vars;
  Cil_datatype.Varinfo.Hashtbl.iter
    (fun v vb -> if Cil_datatype.Varinfo.Set.mem vb !ignore_vars then
      Cil_datatype.Varinfo.Hashtbl.remove cursor_to_base v) cursor_to_base;

  (* Rewrite cursor variables as offsets from their base variable *)
  let visitor =
    new rewriteCursorIntegers cursor_to_base !assigned_vars
  in
  visitFramacFile (visit_and_push_statements_visitor visitor) file


(*****************************************************************************)
(* Annotate code with strlen.                                                *)
(*****************************************************************************)

(* All annotations are added as hints, by no means they should be trusted
   blindly, but they can be used if they are also proved *)

class annotateCodeStrlen(strlen : logic_info) =

  (* Store correspondance from temporaries to the corresponding string access *)

  let temps = Cil_datatype.Varinfo.Hashtbl.create 17 in

  (* Recognize access or test of string *)

  (* TODO: extend applicability of [destruct_string_access]. *)
  let lval_destruct_string_access ~through_tmp = function
    | Mem e, NoOffset when isCharPtrType(typeOf e) ->
	begin match destruct_pointer e with
	  | None -> None
	  | Some(v,Some off) -> Some(v,off)
	  | Some(v,None) -> Some(v,constant_expr Integer.zero)
	end
    | Var v, off ->
	if isCharPtrType v.vtype then
	  match off with
	    | Index(i,NoOffset) -> Some (v,i)
	    | NoOffset
	    | Index _
	    | Field _ -> None
	else if isCharArrayType v.vtype then
	  match off with
	    | Index(i,NoOffset) -> Some (v,i)
	    | NoOffset
	    | Index _
	    | Field _ -> None
	else if through_tmp then
	  try Some(Cil_datatype.Varinfo.Hashtbl.find temps v) with Not_found -> None
	else None
    | _ -> None
  in
  let rec destruct_string_access ?(through_tmp=false) ?(through_cast=false) e =
    match e.enode with
      | Lval lv -> lval_destruct_string_access ~through_tmp lv
      | CastE(_,e) ->
	  if through_cast then
	    destruct_string_access ~through_tmp ~through_cast e
	  else None
      | _ -> None
  in
  let destruct_string_test ?(neg=false) e =
    let rec aux ~neg e = match e.enode with
      | UnOp(LNot,e,_) -> aux ~neg:(not neg) e
      | BinOp(Ne,e1,e2,_) when is_null_expr e2 -> aux ~neg e1
      | BinOp(Ne,e2,e1,_) when is_null_expr e2 -> aux ~neg e1
      | BinOp(Eq,e1,e2,_) when is_null_expr e2 -> aux ~neg:(not neg) e1
      | BinOp(Eq,e2,e1,_) when is_null_expr e2 -> aux ~neg:(not neg) e1
      | _ ->
	  match
            destruct_string_access ~through_tmp:true ~through_cast:true e
	  with
	    | Some(v,off) -> Some(neg,v,off)
	    | None -> None
    in match e.enode with
      | BinOp(Eq,e1,e2,_) when is_non_null_expr e2 -> false, aux ~neg e1
      | BinOp(Eq,e2,e1,_) when is_non_null_expr e2 -> false, aux ~neg e1
      | _ -> true, aux ~neg e
  in

  (* Generate appropriate assertion *)

  let strlen_type =
    match strlen.l_type with Some t -> t | None -> assert false
  in

  let within_bounds ~strict v off =
    let rel1 =
      Logic_const.new_predicate (Logic_const.prel (Rle,lzero(),off))
    in
    let tv = term_of_var v in
    let app2 = mkterm (Tapp(strlen,[],[tv])) strlen_type  v.vdecl in
    let op = if strict then Rlt else Rle in
    let rel2 =
      Logic_const.new_predicate (Logic_const.prel (op,off,app2))
    in
    let app =
      Logic_const.new_predicate
	(Logic_const.pand (Logic_const.pred_of_id_pred rel1,
			   Logic_const.pred_of_id_pred rel2))
    in
    Logic_const.pred_of_id_pred
      { app with ip_name = [ name_of_hint_assertion ] }
  in
  let reach_upper_bound ~loose v off =
    let tv = term_of_var v in
    let app = mkterm (Tapp(strlen,[],[tv])) strlen_type v.vdecl in
    let op = if loose then Rle else Req in
    let rel =
      Logic_const.new_predicate (Logic_const.prel (op,app,off))
    in
    Logic_const.pred_of_id_pred
      { rel with ip_name = [ name_of_hint_assertion ] }
  in
object(self)

  inherit Visitor.frama_c_inplace

  method vexpr e =
    begin match destruct_string_access e with None -> () | Some(v,off) ->
      if hasAttribute name_of_string_declspec (typeAttrs v.vtype) then
	(* A string should be accessed within its bounds *)
	let off = Common.force_exp_to_term off in
	let app = within_bounds ~strict:false v off in
	let cur_stmt = the self#current_stmt in
        let kf = the self#current_kf in
	Annotations.add_assert Common.jessie_emitter ~kf cur_stmt app
    end;
    DoChildren

  method vstmt_aux s =
    let preaction s = match s.skind with
      | If(e,tbl,fbl,_loc) ->
	  begin match destruct_string_test e with _,None -> ()
	    | test_to_null,Some(neg,v,off) ->
		if hasAttribute name_of_string_declspec (typeAttrs v.vtype)
		then
		  (* A string should be tested within its bounds, and
		     depending on the result, the offset is either before
		     or equal to the length of the string *)
		  let off = Common.force_exp_to_term off in
		  let rel1 = within_bounds ~strict:true v off in
		  let supst = mkStmt(Instr(Skip(CurrentLoc.get()))) in
                  let kf = the self#current_kf in
		  Annotations.add_assert Common.jessie_emitter ~kf supst rel1;
		  let rel2 = reach_upper_bound ~loose:false v off in
		  let eqst = mkStmt(Instr(Skip(CurrentLoc.get()))) in
		  Annotations.add_assert Common.jessie_emitter ~kf eqst rel2;

		  (* Rather add skip statement as blocks may be empty *)
		  if neg then
		    begin
		      fbl.bstmts <- supst :: fbl.bstmts;
		      if test_to_null then tbl.bstmts <- eqst :: tbl.bstmts
		    end
		  else
		    begin
		      tbl.bstmts <- supst :: tbl.bstmts;
		      if test_to_null then fbl.bstmts <- eqst :: fbl.bstmts
		    end
	  end; s
      | Instr(Set(lv,e,loc)) when is_null_expr e ->
	  if Jessie_options.HintLevel.get () > 1 then
	    match lval_destruct_string_access ~through_tmp:true lv with
	      | None -> ()
	      | Some(v,off) ->
		  let off = Common.force_exp_to_term off in
		  (* Help ATP with proving the bound on [strlen(v)] by
		     asserting the obvious equality *)
		  let lv' = Common.force_lval_to_term_lval lv in
		  let e' = Common.force_exp_to_term e in
		  let lvt = mkterm (TLval lv') strlen_type loc in
		  let rel =
		    Logic_const.new_predicate (Logic_const.prel (Req,lvt,e'))
		  in
		  let prel =
		    Logic_const.pred_of_id_pred
		      { rel with ip_name = [ name_of_hint_assertion ] }
		  in
                  let kf = the self#current_kf in
		  Annotations.add_assert Common.jessie_emitter ~kf s prel;
		  (* If setting a character to zero in a buffer, this should
		     be the new length of a string *)
		  let rel = reach_upper_bound ~loose:true v off in
		  Annotations.add_assert Common.jessie_emitter ~kf s rel
	  else ();
	  s
      | Instr(Set((Var v1,NoOffset),e,_loc)) ->
	  begin match
	    destruct_string_access ~through_tmp:true ~through_cast:true e
	  with
	    | None -> ()
	    | Some(v2,off) -> Cil_datatype.Varinfo.Hashtbl.add temps v1 (v2,off)
	  end; s
      | _ -> s
    in
    ChangeDoChildrenPost(preaction s,fun x -> x)

 end

let annotate_code_strlen file =
  try
    let strlen =
      match Logic_env.find_all_logic_functions name_of_strlen with
	| [i] -> i
	| _  -> assert false
    in
    let visitor = new annotateCodeStrlen strlen in
    visitFramacFile visitor file
  with Not_found -> assert false


(*****************************************************************************)
(* Annotate code with overflow checks.                                       *)
(*****************************************************************************)

class annotateOverflow =
object(self)

  inherit Visitor.frama_c_inplace

  method vexpr e = 
    match e.enode with
    | BinOp((Shiftlt | Shiftrt as op),e1,e2,_ty) ->
        let kf = the self#current_kf in
	let cur_stmt = the self#current_stmt in
	let is_left_shift = match op with Shiftlt -> true | _ -> false in
	let ty1 = typeOf e1 in
	(* Ideally, should strip only casts introduced by the compiler, not
	 * user casts. Since this information is not available, be
	 * conservative here.
	 *)
	let e1' = stripCastsButLastInfo e1 in
	let e2' = stripCastsButLastInfo e2 in
	(* Check that signed shift has a positive right operand *)
	if isSignedInteger ty1 then
	  begin match possible_value_of_integral_expr e2' with
	    | Some i when Integer.ge i Integer.zero -> ()
	    | _ ->
		let check =
                  new_exp ~loc:e.eloc (BinOp(Ge,e2',
                                             constant_expr Integer.zero,
                                             intType))
                in
		let check = Common.force_exp_to_predicate check in
		Annotations.add_assert Common.jessie_emitter ~kf cur_stmt check
	  end
	else ();
	(* Check that shift has not too big a right operand. *)
	let max_right = Integer.of_int (integral_type_size_in_bits ty1) in
	begin match possible_value_of_integral_expr e2' with
	  | Some i when Integer.lt i max_right -> ()
	  | _ ->
	      let max_right = constant_expr max_right in
	      let check =
                new_exp ~loc:e.eloc (BinOp(Lt,e2',max_right,intType)) in
	      let check = Common.force_exp_to_predicate check
	      in
	      Annotations.add_assert Common.jessie_emitter ~kf cur_stmt check
	end;
	(* Check that signed left shift has a positive left operand *)
	if is_left_shift && isSignedInteger ty1 then
	  begin match possible_value_of_integral_expr e1' with
	    | Some i when Integer.ge i Integer.zero -> ()
	    | _ ->
		let check =
                  new_exp ~loc:e.eloc
                    (BinOp(Ge,e1',constant_expr Integer.zero,intType)) in
		let check = Common.force_exp_to_predicate check
		in
		Annotations.add_assert Common.jessie_emitter ~kf cur_stmt check
	  end
	else ();
	(* Check that signed left shift has not a left operand that is bigger
	 * than the maximal value for the type right shifted by its right
	 * operand.
	 *)
	if is_left_shift && isSignedInteger ty1 then
	  let max_int = max_value_of_integral_type ty1 in
	  begin match possible_value_of_integral_expr e2' with
	    | Some i when Integer.ge i Integer.zero && 
                Integer.lt i (Integer.of_int 64) ->
		let max_left = constant_expr (Integer.shift_right max_int i)
                in
		let check =
                  new_exp ~loc:e.eloc (BinOp(Le,e1',max_left,intType))
                in
		let check = Common.force_exp_to_predicate check in
		Annotations.add_assert Common.jessie_emitter ~kf cur_stmt check
	    | _ ->
		let max_int = constant_expr max_int in
		let max_left =
                  new_exp ~loc:e.eloc (BinOp(Shiftrt,max_int,e2',intType))
                in
		let check = new_exp ~loc:e.eloc
                  (BinOp(Le,e1',max_left,intType))
                in
		let check = Common.force_exp_to_predicate check in
		Annotations.add_assert Common.jessie_emitter ~kf cur_stmt check
	  end
	else ();
	DoChildren
    | _ -> DoChildren

end

let annotate_overflow file =
  let visitor = new annotateOverflow in
  visitFramacFile visitor file


(*****************************************************************************)
(* Rewrite type void* into char*.                                            *)
(*****************************************************************************)

class rewriteVoidPointer =
object

  inherit Visitor.frama_c_inplace

  method vtype ty =
    if isVoidPtrType ty then
      let attr = typeAttr ty in
      ChangeTo (typeAddAttributes attr charPtrType)
(*
    else if isCharType ty then
      (* Yannick: All (un)signed chars changed into char for now ...
	 Claude: why ????
      *)
      let attr = typeAttr ty in
      ChangeTo (typeAddAttributes attr charType)
*)
    else DoChildren

end

class debugVoid =
object
  inherit Visitor.frama_c_inplace
  method vterm ts = match ts.term_node with
    | TLval(TResult _,_) -> DoChildren
    | _ ->
	assert (not (app_term_type isVoidPtrType false ts.term_type));
	DoChildren
end

let rewrite_void_pointer file =
  let visitor = new rewriteVoidPointer in
  visitFramacFile visitor file

(* Jessie/Why has trouble with Pre labels inside function contracts. *)
class rewritePreOld : Visitor.frama_c_visitor =
object(self)
  inherit Visitor.frama_c_inplace
  val mutable rep_lab = Logic_const.pre_label
    method vbehavior b =
      rep_lab <- Logic_const.here_label;
      let requires = 
        Visitor.visitFramacPredicates 
          (self:>Visitor.frama_c_visitor) b.b_requires 
      in
      let assumes =
        Visitor.visitFramacPredicates 
          (self:>Visitor.frama_c_visitor) b.b_assumes
      in
      let allocation =
        match b.b_allocation with
          | FreeAllocAny -> FreeAllocAny
          | FreeAlloc(free,alloc) ->
              rep_lab <- Logic_const.here_label;
              let free = 
                List.map 
                  (Visitor.visitFramacIdTerm 
                     (self:>Visitor.frama_c_visitor))
                  free
              in
              rep_lab <- Logic_const.old_label;
              let alloc =
                List.map
                  (Visitor.visitFramacIdTerm
                     (self:>Visitor.frama_c_visitor))
                  alloc
              in
              FreeAlloc(free,alloc)
      in
      (* VP: 2012-09-20: signature of Cil.mk_behavior is utterly broken.
         We'll have to live with that for Oxygen, but this will change as
         soon as possible. *)
      let allocation = Some allocation in
      rep_lab <- Logic_const.old_label;
      let assigns =
        Visitor.visitFramacAssigns 
          (self:>Visitor.frama_c_visitor) b.b_assigns
      in
      let post_cond = 
        Cil.mapNoCopy 
          (fun (k,p as e) -> 
            let p' = 
              Visitor.visitFramacIdPredicate 
                (self:>Visitor.frama_c_visitor) p
            in
            if p != p' then (k,p') else e)
          b.b_post_cond
      in
      rep_lab <- Logic_const.pre_label;
      let name = b.b_name in
      let b = Cil.mk_behavior
        ~name ~requires ~assumes ~assigns ~allocation ~post_cond () in
      ChangeTo b

  method vlogic_label l =
    if Cil_datatype.Logic_label.equal l Logic_const.pre_label
       && self#current_kinstr = Kglobal (* Do not rewrite Pre in stmt annot. *)
    then
      ChangeTo rep_lab
    else DoChildren
end

let rewrite_pre_old file =
  let visitor = new rewritePreOld in
  visitFramacFile visitor file

class remove_unsupported: Visitor.frama_c_visitor =
object
  inherit Visitor.frama_c_inplace
  method vpredicate =
    function
      | Pseparated _ ->
          Jessie_options.warning ~once:true
            "\\separated is not supported by Jessie. This predicate will be \
             ignored";
          ChangeTo Ptrue
      | _ -> DoChildren
end

let remove_unsupported file =
  let visitor = new remove_unsupported in
  visitFramacFile visitor file

(*****************************************************************************)
(* Rewrite comprehensions into ranges (and back)                             *)
(*****************************************************************************)

let rec add_range vi t1opt t2opt = ranges := (vi,t1opt,t2opt) :: !ranges
and no_range_offset = function
TNoOffset -> true
  | TField(_,offs) | TModel(_,offs) -> no_range_offset offs
  | TIndex({term_type = Ltype ({ lt_name = "set"},[_])},_) -> false
  | TIndex(_,offs) -> no_range_offset offs
and make_comprehension ts =
  let ts = match ts.term_node with
      TLval(ts',offs) when no_range_offset offs ->
        (match ts' with
        | TMem { term_type = Ltype ({lt_name = "set"},[_])} -> ts
        | TMem _ | TVar _ | TResult _ ->
          { ts with term_type = Logic_const.type_of_element ts.term_type}
        )
    | _ -> ts
  in
  let loc = ts.term_loc in
  let ts =
    List.fold_left
      (fun ts (v,t1opt,t2opt) ->
         let vt = variable_term loc v in
         let popt = match t1opt,t2opt with
           | None,None -> None
           | Some t1,None -> Some(predicate t1.term_loc (Prel(Rle,t1,vt)))
           | None,Some t2 -> Some(predicate t2.term_loc (Prel(Rle,vt,t2)))
           | Some t1,Some t2 ->
               let p1 = predicate t1.term_loc (Prel(Rle,t1,vt)) in
               let p2 = predicate t2.term_loc (Prel(Rle,vt,t2)) in
               let loc = (fst t1.term_loc, snd t2.term_loc) in
               Some(predicate loc (Pand(p1,p2)))
         in
         (* NB: no need to update the type, as it is already
            a set of terms (for well-formed terms at least) *)
         { ts with term_node = Tcomprehension(ts,[v],popt) }
      ) ts !ranges
  in
  ranges := [];
  ts
and ranges = ref []


class fromRangeToComprehension behavior = object

  inherit Visitor.generic_frama_c_visitor behavior

  method vterm ts = match ts.term_type with
    | Ltype ({ lt_name = "set"},[_]) ->
      ChangeDoChildrenPost(ts, make_comprehension)
    | _ -> DoChildren

  method vterm_offset tsoff = match tsoff with
    | TIndex ({ term_node =Trange(t1opt,t2opt)} as t,tsoff') ->
        let v = make_temp_logic_var Linteger in
        add_range v t1opt t2opt;
        let vt = variable_term t.term_loc v in
        ChangeDoChildrenPost (TIndex(vt,tsoff'), fun x -> x)
    | TNoOffset | TIndex _ | TField _ | TModel _ -> DoChildren

end

let from_range_to_comprehension behavior file =
  let visitor = new fromRangeToComprehension behavior in
  Visitor.visitFramacFile visitor file

let range_to_comprehension t =
  let visitor =
    new fromRangeToComprehension (Cil.copy_visit (Project.current ()))
  in
  Visitor.visitFramacTerm visitor t


class fromComprehensionToRange behavior =
  let ranges = Logic_var.Hashtbl.create 17 in
  let add_range vi t1opt t2opt =
    Logic_var.Hashtbl.add ranges vi (t1opt,t2opt)
  in
  let index_variables_of_term ts =
    let vars = ref Logic_var.Set.empty in
    ignore
      (visitCilTerm
         (object
           inherit nopCilVisitor
           method vterm = function
           | { term_node =
               TBinOp(PlusPI,_ts,{term_node=TLval(TVar v,TNoOffset)})} ->
             vars := Logic_var.Set.add v !vars;
             DoChildren
           | _ -> DoChildren
           method vterm_offset = function
           | TIndex({term_node=TLval(TVar v,TNoOffset)},_tsoff) ->
             vars := Logic_var.Set.add v !vars;
             DoChildren
           | _ -> DoChildren
          end)
        ts);
    !vars
  in
  let bounds_of_variable v popt =
    let error () =
      Kernel.fatal "Cannot identify bounds for variable %s" v.lv_name
    in
    let rec bounds p =
      match p.content with
      | Prel(Rle, {term_node = TLval(TVar v',TNoOffset)}, t)
          when Logic_var.equal v v' ->
        None, Some t
      | Prel(Rle, t, {term_node = TLval(TVar v',TNoOffset)})
          when Logic_var.equal v v' ->
        Some t, None
      | Pand(p1,p2) ->
        begin match bounds p1, bounds p2 with
        | (Some t1, None),(None, Some t2) | (None, Some t2),(Some t1, None) ->
          Some t1, Some t2
        | _ -> error ()
        end
      | _ -> error ()
    in
    match popt with None -> None, None | Some p -> bounds p
  in
object(self)

  inherit Visitor.generic_frama_c_visitor behavior

  val mutable has_set_type = false

  method private propagate_set_type t =
    if has_set_type then
      { t with term_type = Logic_const.make_set_type t.term_type }
    else t

  method vterm t = match t.term_node with
    | Tcomprehension(ts,[v],popt) ->
        let index_vars = index_variables_of_term ts in
        (* Only accept for now comprehension on index variables *)
        if Logic_var.Set.mem v index_vars then begin
          let t1opt,t2opt = bounds_of_variable v popt in
          add_range v t1opt t2opt;
          has_set_type <- false;
          ChangeTo (visitCilTerm (self :> cilVisitor) ts)
        end else begin
          has_set_type <- false;
          DoChildren
        end
    | TBinOp(PlusPI,base,{term_node=TLval(TVar v,TNoOffset)}) ->
          begin try
            let low,high = Logic_var.Hashtbl.find ranges v in
            let range = Logic_const.trange (low,high) in
            let res =
            { t with
                term_node = TBinOp(PlusPI,base,range);
                term_type = Logic_const.make_set_type t.term_type }
            in
            ChangeDoChildrenPost (res, fun x -> has_set_type <- true; x)
          with Not_found -> DoChildren end

    | TBinOp(bop,t1,t2) ->
        has_set_type <- false;
        let t1' = visitCilTerm (self:>Cil.cilVisitor) t1 in
        let has_set_type1 = has_set_type in
        let t2' = visitCilTerm (self:>Cil.cilVisitor) t2 in
        has_set_type <- has_set_type || has_set_type1;
        if t1 != t1' || t2 != t2' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = TBinOp(bop,t1',t2')})
        else SkipChildren
    | Tapp(f,prms,args) ->
        has_set_type <- false;
        let visit t =
          let has_set_type1 = has_set_type in
          let res = visitCilTerm (self:>cilVisitor) t in
          has_set_type <- has_set_type || has_set_type1; res
        in
        let args' = mapNoCopy visit args in
        if args != args' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = Tapp(f,prms,args') })
        else SkipChildren
     | TDataCons(c,args) ->
        has_set_type <- false;
        let visit t =
          let has_set_type1 = has_set_type in
          let res = visitCilTerm (self:>cilVisitor) t in
          has_set_type <- has_set_type || has_set_type1; res
        in
        let args' = mapNoCopy visit args in
        if args != args' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = TDataCons(c,args') })
        else SkipChildren
     | Tif (t1,t2,t3) ->
        has_set_type <- false;
        let t1' = visitCilTerm (self:>Cil.cilVisitor) t1 in
        let has_set_type1 = has_set_type in
        let t2' = visitCilTerm (self:>Cil.cilVisitor) t2 in
        let has_set_type1 = has_set_type || has_set_type1 in
        let t3' = visitCilTerm (self:>Cil.cilVisitor) t3 in
        has_set_type <- has_set_type || has_set_type1;
        if t1 != t1' || t2 != t2' || t3!=t3' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = Tif(t1',t2',t3')})
        else SkipChildren
     | TCoerceE(t1,t2) ->
        has_set_type <- false;
        let t1' = visitCilTerm (self:>Cil.cilVisitor) t1 in
        let has_set_type1 = has_set_type in
        let t2' = visitCilTerm (self:>Cil.cilVisitor) t2 in
        has_set_type <- has_set_type || has_set_type1;
        if t1 != t1' || t2 != t2' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = TCoerceE(t1',t2')})
        else SkipChildren
     | Tunion l ->
       has_set_type <- false;
        let visit t =
          let has_set_type1 = has_set_type in
          let res = visitCilTerm (self:>cilVisitor) t in
          has_set_type <- has_set_type || has_set_type1; res
        in
        let l' = mapNoCopy visit l in
        if l != l' || has_set_type then
          ChangeTo
             (self#propagate_set_type { t with term_node = Tunion l' })
        else SkipChildren
     | Tinter l ->
       has_set_type <- false;
        let visit t =
          let has_set_type1 = has_set_type in
          let res = visitCilTerm (self:>cilVisitor) t in
          has_set_type <- has_set_type || has_set_type1; res
        in
        let l' = mapNoCopy visit l in
        if l != l' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = Tinter l' })
        else SkipChildren
     | Trange(t1,t2) ->
        has_set_type <- false;
        let t1' = optMapNoCopy (visitCilTerm (self:>Cil.cilVisitor)) t1 in
        let has_set_type1 = has_set_type in
        let t2' = optMapNoCopy (visitCilTerm (self:>Cil.cilVisitor)) t2 in
        has_set_type <- has_set_type || has_set_type1;
        if t1 != t1' || t2 != t2' || has_set_type then
          ChangeTo
            (self#propagate_set_type { t with term_node = Trange(t1',t2')})
        else SkipChildren
     | _ ->
         has_set_type <- false;
         ChangeDoChildrenPost (t,self#propagate_set_type)

  method vterm_lval (lh,lo) =
    let lh' = visitCilTermLhost (self:>Cil.cilVisitor) lh in
    let has_set_type1 = has_set_type in
    let lo' = visitCilTermOffset (self :> Cil.cilVisitor) lo in
    has_set_type <- has_set_type || has_set_type1;
    if lh' != lh || lo' != lo then ChangeTo (lh',lo') else SkipChildren

  method vterm_lhost = function
    | TVar v ->
        if Logic_var.Hashtbl.mem ranges v then begin
          Format.eprintf "vterm_lhost: Found: v = %s@." v.lv_name;
          assert false
        end;
        DoChildren
    | _ -> DoChildren

  method vterm_offset off =
    match off with
      | TIndex({term_node=TLval(TVar v,TNoOffset)} as idx,off') ->
          begin try
            let t1opt,t2opt = Logic_var.Hashtbl.find ranges v in
            let trange = Trange(t1opt,t2opt) in
            let toff =
              TIndex
                ({ idx with
                  term_node = trange;
                  term_type = Logic_const.make_set_type idx.term_type },
                 off')
            in
            ChangeDoChildrenPost (toff, fun x -> x)
          with Not_found ->
            DoChildren end
      | TIndex _ | TNoOffset | TField _ | TModel _ ->
          DoChildren

end

let from_comprehension_to_range behavior file =
  let visitor = new fromComprehensionToRange behavior in
  Visitor.visitFramacFile visitor file


(*****************************************************************************)
(* Rewrite the C file for Jessie translation.                                *)
(*****************************************************************************)

let rewrite file =
  if checking then check_types file;
  (* adds a behavior named [name_of_default_behavior] to all functions if
     it does not already exist.
   *)
  Jessie_options.debug "Adding default behavior to all functions";
  add_default_behavior ();
  if checking then check_types file;
  (* Rename entities to avoid conflicts with Jessie predefined names.
     Should be performed before any call to [Cil.cvar_to_lvar] destroys
     sharing among logic variables.
  *)
  Jessie_options.debug "Rename entities";
  rename_entities file;
  if checking then check_types file;
  (* Fill offset/size information in fields *)
  Jessie_options.debug "Fill offset/size information in fields";
  fill_offset_size_in_fields file;
  if checking then check_types file;
  (* Replace addrof array with startof. *)
  Jessie_options.debug "Replace addrof array with startof";
  replace_addrof_array file;
  if checking then check_types file;
  (* Replace string constants by global variables. *)
  Jessie_options.debug "Replace string constants by global variables";
  replace_string_constants file;
  if checking then check_types file;
  (* Put all global initializations in the [globinit] file. *)
  (* Replace global compound initializations by equivalent statements. *)
  Jessie_options.debug "Put all global initializations in the [globinit] file";
  gather_initialization file;
  if checking then check_types file;
  Jessie_options.debug "Use specialized versions of Frama_C_memset";
  specialize_memset file;
  if checking then check_types file;
  (* Rewrite comparison of pointers into difference of pointers. *)
  if Jessie_options.InferAnnot.get () <> "" then
    begin
      Jessie_options.debug "Rewrite comparison of pointers into difference of pointers";
      rewrite_pointer_compare file;
      if checking then check_types file
    end;
  (* Rewrite type void* and (un)signed char* into char*. *)
  Jessie_options.debug "Rewrite type void* and (un)signed char* into char*";
  rewrite_void_pointer file;
  if checking then check_types file;
  Jessie_options.debug "Rewrite Pre as Old in funspec";
  rewrite_pre_old file;
  if checking then check_types file;
  (* Rewrite cursor pointers into offsets from base pointers. *)
  (* order: after [rewrite_pointer_compare] *)
  if Jessie_options.InferAnnot.get () <> "" then
    begin
      Jessie_options.debug "Rewrite cursor pointers into offsets from base pointers";
      rewrite_cursor_pointers file;
      if checking then check_types file
    end;
  (* Rewrite cursor integers into offsets from base integers. *)
  if Jessie_options.InferAnnot.get () <> "" then
    begin
      Jessie_options.debug "Rewrite cursor integers into offsets from base integers";
      rewrite_cursor_integers file;
      if checking then check_types file
    end;
  (* Annotate code with strlen. *)
  if Jessie_options.HintLevel.get () > 0 then
    begin
      Jessie_options.debug "Annotate code with strlen";
      annotate_code_strlen file;
      if checking then check_types file
    end;
  (* Annotate code with overflow checks. *)
  Jessie_options.debug "Annotate code with overflow checks";
  annotate_overflow file;
  if checking then check_types file;
  Jessie_options.debug "Checking if there are unsupported predicates";
  remove_unsupported file;
  if checking then check_types file

(*
Local Variables:
compile-command: "make -C ."
End:
*)
