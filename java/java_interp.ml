(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

(* $Id: java_interp.ml,v 1.102 2008-01-28 14:12:52 moy Exp $ *)

open Format
open Jc_output
open Jc_env
open Jc_fenv
open Jc_ast
open Jc_pervasives
open Java_env
open Java_ast
open Java_tast
open Java_pervasives
open Java_typing

let reg_loc ?id ?kind ?name loc = Output.reg_loc "K" ?id ?kind ?name loc

(*s loop tags *)

let get_loop_counter = 
  let counter = ref 0 in
  function () -> let tag = !counter in incr counter; tag

(*s range types *)

(* byte = int8 *)
let byte_range =
  {
    jc_enum_info_name = "byte";
    jc_enum_info_min = min_byte;
    jc_enum_info_max = max_byte;
  }

(* short = int16 *)
let short_range =
  {
    jc_enum_info_name = "short";
    jc_enum_info_min = min_short;
    jc_enum_info_max = max_short;
  }

(* int = int32 *)
let int_range =
  {
    jc_enum_info_name = "int32";
    jc_enum_info_min = min_int;
    jc_enum_info_max = max_int;
  }

(* long = int64 *)
let long_range =
  {
    jc_enum_info_name = "long";
    jc_enum_info_min = min_long;
    jc_enum_info_max = max_long;
  }

(* char = uint16 *)
let char_range =
  {
    jc_enum_info_name = "char";
    jc_enum_info_min = min_char;
    jc_enum_info_max = max_char;
  }

let range_types acc =
  if !Java_options.ignore_overflow then acc else
  List.fold_left
    (fun acc ri ->
       JCenum_type_def(ri.jc_enum_info_name,
			ri.jc_enum_info_min,
			ri.jc_enum_info_max)::acc) 
    acc [ byte_range ; short_range ; int_range ; long_range ; char_range ]


let byte_type = JCTenum byte_range
let short_type = JCTenum short_range 
let int_type = JCTenum int_range 
let long_type = JCTenum long_range 
let char_type = JCTenum char_range 

let get_enum_info t =
  match t with
    | Tshort -> short_range
    | Tint -> int_range
    | Tlong -> long_range
    | Tchar -> char_range
    | Tbyte -> byte_range
    | _ -> assert false

let tr_base_type t =
  match t with
    | Tunit -> Jc_pervasives.unit_type
    | Tboolean -> Jc_pervasives.boolean_type
    | Tinteger -> Jc_pervasives.integer_type
    | Tshort -> 
	if !Java_options.ignore_overflow then Jc_pervasives.integer_type else
	short_type
    | Tint -> 
	if !Java_options.ignore_overflow then Jc_pervasives.integer_type else
	int_type
    | Tlong -> 
	if !Java_options.ignore_overflow then Jc_pervasives.integer_type else
	long_type
    | Tchar -> 
	if !Java_options.ignore_overflow then Jc_pervasives.integer_type else
	char_type
    | Tbyte  -> 
	if !Java_options.ignore_overflow then Jc_pervasives.integer_type else
	byte_type
    | Treal -> Jc_pervasives.real_type
    | Tfloat -> assert false (* TODO *)
    | Tdouble -> assert false (* TODO *)

(*s class types *)

let rec object_variant = {
  jc_variant_info_name = "Object";
  jc_variant_info_roots = [ object_root ];
}

and object_root = {
  jc_struct_info_name = "Object";
  jc_struct_info_parent = None;
  jc_struct_info_root = object_root;
  jc_struct_info_fields = [];
  jc_struct_info_variant = Some object_variant;
}

let get_class ci =
  {
    jc_struct_info_name = ci.class_info_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = object_root;
    jc_struct_info_fields = [];
    jc_struct_info_variant = Some object_variant;
  }

(*
let get_interface ii =
  {
    jc_struct_info_name = ii.interface_info_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = ii.interface_info_name;
    jc_struct_info_fields = [];
  }
*)

let rec interface_root = {
  jc_struct_info_name = "interface";
  jc_struct_info_parent = None;
  jc_struct_info_root = interface_root;
  jc_struct_info_fields = [];
  jc_struct_info_variant = Some object_variant;
}

let st_interface = 
  {
    jc_struct_info_name = "interface";
    jc_struct_info_parent = None;
    jc_struct_info_root = interface_root;
    jc_struct_info_fields = [];
    jc_struct_info_variant = Some object_variant;
  }

(*s array types *)

let num_zero = Num.Int 0
let num_minus_one = Num.Int (-1)

let array_struct_table = Hashtbl.create 17
      
let rec get_array_struct loc t = 
  try
    Hashtbl.find array_struct_table t 
  with Not_found -> 
    eprintf "Array struct for type %a not found: %a@." 
      Java_typing.print_type t Loc.report_position loc;
    raise Not_found

and tr_type loc t =
  match t with
    | JTYbase t -> tr_base_type t	
    | JTYnull -> JCTnull
    | JTYclass (non_null, ci) -> 
	let st = get_class ci in
	  JCTpointer 
	    (st, Some num_zero, if non_null then Some num_zero else None)
    | JTYinterface ii ->
	JCTpointer(st_interface, Some num_zero,None)
(*
	let st = get_interface ii in
	JCTpointer(st,Some num_zero,
	           (* if non_null then Some num_zero else *) None)
*)
	
    | JTYarray t ->
	let st = get_array_struct loc t in
	JCTpointer(st,Some num_zero,None)

let tr_type_option loc t =
  match t with
    | None -> Jc_pervasives.unit_type
    | Some t -> tr_type loc t

(*s structure fields *)

let fi_table = Hashtbl.create 97

let get_field fi =
  try
    Hashtbl.find fi_table fi.java_field_info_tag
  with
      Not_found -> 
	eprintf "Internal error: field '%s' not found@." 
	  fi.java_field_info_name;
	assert false

let create_field loc fi =
  Java_options.lprintf "Creating JC field '%s'@." fi.java_field_info_name;
  let ty = tr_type loc fi.java_field_info_type in
  let ci = 
    match fi.java_field_info_class_or_interface with
      | TypeClass ci -> get_class ci
      | TypeInterface _ -> assert false
  in
  let nfi =
    { jc_field_info_name = fi.java_field_info_name;
      jc_field_info_final_name = fi.java_field_info_name;
      jc_field_info_tag  = fi.java_field_info_tag;
      jc_field_info_type = ty;
      jc_field_info_root = ci.jc_struct_info_root;
      jc_field_info_struct = ci;
      jc_field_info_rep = false;
      (*
	jc_field_info_final_name = vi.java_field_info_name;
	jc_var_info_assigned = vi.java_var_info_assigned;
	jc_var_info_type = tr_type vi.java_var_info_type;
	jc_var_info_tag = vi.java_var_info_tag;
      *)
    }
  in Hashtbl.add fi_table fi.java_field_info_tag nfi;
  nfi

let static_fields_table = Hashtbl.create 97

let get_static_var fi =
  try
    Hashtbl.find static_fields_table fi.java_field_info_tag
  with
      Not_found -> 
	eprintf "Java_interp.get_static_var->Not_found: %s@." fi.java_field_info_name;
	raise Not_found
 

(* local variables and parameters *)

let vi_table = Hashtbl.create 97

let get_var vi =
  try
    Hashtbl.find vi_table vi.java_var_info_tag
  with
      Not_found -> 
	eprintf "Java_interp.get_var->Not_found: '%s', %a@." 
	  vi.java_var_info_final_name
	  Loc.report_position vi.java_var_info_decl_loc
	;
	raise Not_found

let create_var ?(formal=false) loc vi =
  let ty = tr_type loc vi.java_var_info_type in
  let nvi = Jc_pervasives.var ~formal ty vi.java_var_info_final_name in
  nvi.jc_var_info_assigned <- vi.java_var_info_assigned;
  Hashtbl.add vi_table vi.java_var_info_tag nvi;
  nvi

(*s logic funs *)

let logics_table = Hashtbl.create 97

let get_logic_fun fi =
  try
    Hashtbl.find logics_table fi.java_logic_info_tag
  with
      Not_found -> 
	eprintf "Anomaly: cannot find logic symbol `%s'@." fi.java_logic_info_name;
	assert false

let tr_logic_label = function
  | LabelPre -> Jc_env.LabelPre
  | LabelHere -> Jc_env.LabelHere
  | LabelPost -> Jc_env.LabelPost
  | LabelName s -> Jc_env.LabelName s

let create_logic_fun loc fi =
  let nfi =
    match fi.java_logic_info_result_type with
      | None ->
	  Jc_pervasives.make_rel fi.java_logic_info_name 
      | Some t ->
	  Jc_pervasives.make_logic_fun fi.java_logic_info_name 
	    (tr_type loc t) 
  in
  nfi.jc_logic_info_parameters <-
    List.map (create_var loc) fi.java_logic_info_parameters;
  nfi.jc_logic_info_labels <- 
    List.map tr_logic_label fi.java_logic_info_labels;
  Hashtbl.add logics_table fi.java_logic_info_tag nfi;
  nfi

(*s program funs *)

let funs_table = Hashtbl.create 97

let get_fun loc tag =
  try
    Hashtbl.find funs_table tag
  with
      Not_found -> 
	eprintf "Java_interp.get_fun->Not_found: %a@." Loc.report_position loc;
	raise Not_found

let create_fun loc tag result name params =
  let nfi =
    match result with
      | None ->
	  Jc_pervasives.make_fun_info name 
	    Jc_pervasives.unit_type
      | Some vi ->
	  Jc_pervasives.make_fun_info name
	    (tr_type loc vi.java_var_info_type) 
  in
  nfi.jc_fun_info_parameters <-
    List.map (create_var loc) params;
  Hashtbl.add funs_table tag nfi;
  nfi

(*s exceptions *)

let exceptions_table = Hashtbl.create 17 

let get_exception ty =
  match ty with
    | JTYclass(_,ci) ->
	begin
	  try
	    Hashtbl.find exceptions_table ci.class_info_name
	  with
	      Not_found -> 
		eprintf "exception %s not found@." ci.class_info_name;
		assert false
	end
    | _ -> assert false

let exceptions_tag = ref 0

let create_exception ty n =
  incr exceptions_tag;
  let ei =
    { jc_exception_info_name = n;
      jc_exception_info_tag = !exceptions_tag;
      jc_exception_info_type = ty     
    }
  in
  Hashtbl.add exceptions_table n ei;
  ei

(*s terms *)

let lit l =
  match l with
  | Integer s -> JCCinteger s
  | Float s -> JCCreal s
  | Bool b -> JCCboolean b
  | String s -> assert false (* TODO *)
  | Char s -> assert false (* TODO *)
  | Null  -> JCCnull

let lun_op t op =
  match op with
    | Unot -> Jc_ast.Unot
    | Uminus when t = Tinteger -> Uminus_int
    | Uminus -> assert false (* TODO *)
    | Uplus -> assert false
    | Ucompl -> Ubw_not

let lbin_op t op =
  match op with
    | Bgt -> Bgt_int
    | Bge -> Bge_int
    | Ble -> Ble_int
    | Blt -> Blt_int
    | Bne -> Bneq_int
    | Beq -> Beq_int
    | Basr -> Barith_shift_right
    | Blsr -> Blogical_shift_right
    | Blsl -> Bshift_left
    | Bbwxor -> Bbw_xor
    | Bbwor -> Bbw_or
    | Bbwand -> Bbw_and
    | Biff|Bimpl|Bor|Band -> assert false (* TODO *)
    | Bmod -> Bmod_int
    | Bdiv -> Bdiv_int
    | Bmul -> Bmul_int
    | Bsub -> Bsub_int
    | Badd -> Badd_int

let lobj_op op =
  match op with
    | Bne -> Bneq_pointer
    | Beq -> Beq_pointer
    | _ -> assert false

(* non_null funs & preds *)
    
let non_null_funs = Hashtbl.create 17
let non_null_preds = Hashtbl.create 17
  
let non_null_fun si =
  try
    Hashtbl.find non_null_funs si.jc_struct_info_name
  with
      Not_found -> assert false

let non_null_pred name =
  try
    Hashtbl.find non_null_preds name
  with
      Not_found -> assert false
	
let create_non_null_fun si =
  let fi = 
    Jc_pervasives.make_fun_info 
      ("non_null_" ^ si.jc_struct_info_name)
      Jc_pervasives.boolean_type
  in
    Hashtbl.add non_null_funs si.jc_struct_info_name fi;
    fi

let create_non_null_pred si =
  let li = 
    Jc_pervasives.make_rel 
      ("Non_null_" ^ si.jc_struct_info_name)
  in
    Hashtbl.add non_null_preds si.jc_struct_info_name li;
    li

let dummy_loc_term ty t =
  { jc_term_loc = Loc.dummy_position; 
    jc_term_label = "";
    jc_term_type = ty;
    jc_term_region = Jc_region.dummy_region;
    jc_term_node = t }

let term_zero = 
  dummy_loc_term Jc_pervasives.integer_type 
    (JCTconst (JCCinteger "0"))

let term_maxint = 
  dummy_loc_term Jc_pervasives.integer_type 
    (JCTconst (JCCinteger "2147483647"))

let term_plus_one t =
  JCTbinary (t, Badd_int, { t with jc_term_node = JCTconst (JCCinteger "1") })

let rec term t =
  let t' =
    match t.java_term_node with
      | JTlit l -> JCTconst (lit l)
      | JTun (t,op,e1) -> JCTunary (lun_op t op, term e1)
      | JTbin(e1,t,op,e2) -> JCTbinary(term e1, lbin_op t op, term e2)
      | JTapp (fi, el) -> 
	  let app = {
	    jc_app_fun = get_logic_fun fi;
	    jc_app_args = List.map term el;
	    jc_app_region_assoc = [];
	    jc_app_label_assoc = [] ;
	  } in
	  JCTapp app
      | JTvar vi -> JCTvar (get_var vi)
      | JTfield_access(t,fi) -> JCTderef(term t,Jc_env.LabelHere,get_field fi)
      | JTstatic_field_access(ci,fi) ->	  
	  JCTvar(get_static_var fi)
      | JTarray_length(t) -> 
	  begin
	    match t.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct t.java_term_loc ty in
		  let t = term t in
		  term_plus_one
		    { t with jc_term_node = JCToffset(Offset_max, t, st) }
	      | _ -> assert false
	  end
      | JTarray_access(t1,t2) -> 
	  begin
	    match t1.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct t.java_term_loc ty in
		  let t1' = term t1 in
		  let shift = {
		    jc_term_loc = t.java_term_loc;
		    jc_term_label = "";
		    jc_term_type = t1'.jc_term_type;
		    jc_term_region = Jc_region.dummy_region;
		    jc_term_node = JCTshift(t1', term t2)
		  }
		  in
		  JCTderef(shift,Jc_env.LabelHere,(List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JTarray_range _ -> assert false
      | JTold t -> JCTold(term t)
      | JTat(t,lab) -> JCTat(term t,tr_logic_label lab)
      | JTcast(ty,t) ->
	  begin
	    match ty with
	      | JTYbase _ -> (term t).jc_term_node
	      | JTYclass(_,ci) ->
		  let st = get_class ci in
		  JCTcast(term t,st)
	      | _ -> assert false (* TODO *)
	  end

  in { jc_term_loc = t.java_term_loc ; 
       jc_term_label = "";
       jc_term_type = tr_type  t.java_term_loc t.java_term_type ;
       jc_term_region = Jc_region.dummy_region;
       jc_term_node = t' }

let quantifier = function
  | Forall -> Jc_ast.Forall
  | Exists -> Jc_ast.Exists

let rec assertion ?(reg=0) a =
  let a' =
    match a.java_assertion_node with
      | JAtrue -> JCAtrue
      | JAfalse -> JCAfalse
      | JAnot a -> JCAnot (assertion a)
      | JAbin (e1, t, op, e2) -> JCArelation(term e1, lbin_op t op, term e2)
      | JAbin_obj (e1, op, e2) -> (* case e1 != null *) 
	  if op = Bne && e2.java_term_node = JTlit Null then
	    let t1 = term e1 in
	    match e1.java_term_type with
	      | JTYbase _ | JTYnull -> assert false
	      | JTYclass (_, ci) ->
		  let app = {
		    jc_app_fun = non_null_pred "Object";
		    jc_app_args = [t1];
		    jc_app_region_assoc = [];
		    jc_app_label_assoc = [] ;
		  } in
		    JCAapp app
(*              	  let offset_maxt = term_no_loc 
		    (JCToffset (Offset_max, t1, st)) Jc_pervasives.integer_type in
		    JCArelation (offset_maxt, Beq_int, zerot) *)
	      | JTYinterface ii ->
		  let si = st_interface in
		  (* let offset_mint = term_no_loc 
		     (JCToffset (Offset_min, t1, st)) Jc_pervasives.integer_type in
		     let offset_mina =
		     raw_asrt (JCArelation (offset_mint, Beq_int, zerot)) 
		     in *)
		  let offset_maxt = term_no_loc 
		    (JCToffset (Offset_max, t1, si)) Jc_pervasives.integer_type in
		  (* let offset_maxa =
		    raw_asrt ( *) JCArelation (offset_maxt, Beq_int, zerot) (* ) 
		  in
		    JCAand [offset_mina; offset_maxa]*)
	      | JTYarray t ->
		  let si = get_array_struct Loc.dummy_position t in
		  let app = {
		    jc_app_fun = non_null_pred si.jc_struct_info_name;
		    jc_app_args = [t1];
		    jc_app_region_assoc = [];
		    jc_app_label_assoc = [] ;
		  } in
		    JCAapp app
(*		  let offset_mint = term_no_loc 
		    (JCToffset (Offset_min, t1, st)) Jc_pervasives.integer_type in
		  let offset_mina =
		    raw_asrt (JCArelation (offset_mint, Beq_int, zerot)) 
		  in
		  let offset_maxt = term_no_loc 
		    (JCToffset (Offset_max, t1, st)) Jc_pervasives.integer_type in
		  let offset_maxa =
		    raw_asrt (JCArelation (offset_maxt, Bge_int, minusonet)) 
		  in
		    JCAand [offset_mina; offset_maxa] *)
	  else
	    JCArelation (term e1, lobj_op op, term e2)
      | JAapp (fi, el)-> 
	  let app = {
	    jc_app_fun = get_logic_fun fi;
	    jc_app_args = List.map term el;
	    jc_app_region_assoc = [];
	    jc_app_label_assoc = [] ;
	  } in
	  JCAapp app
      | JAquantifier (q, vi, a)-> 
	  let vi = create_var a.java_assertion_loc vi in
	    JCAquantifier(quantifier q,vi,assertion a)
      | JAimpl (a1, a2)-> 
	  JCAimplies(assertion a1,assertion a2)
      | JAiff (a1, a2)-> 
	  JCAiff(assertion a1,assertion a2)
      | JAor (a1, a2)-> 
	  JCAor [assertion a1 ; assertion a2]
      | JAand (a1, a2)-> 
          let reg = if reg > 0 then 2 else 0 in
	  JCAand [assertion ~reg a1 ; assertion ~reg a2]
      | JAbool_expr t -> JCAbool_term(term t)
      | JAinstanceof (t, ty) ->
	  let ty = tr_type Loc.dummy_position ty in
	    match ty with
	      | JCTpointer (si, _, _) ->
		  JCAinstanceof (term t, LabelNone, si)
	      | _ -> assert false

  in { jc_assertion_loc = a.java_assertion_loc ; 
       jc_assertion_label = if reg=2 then reg_loc a.java_assertion_loc else "";
       jc_assertion_node = a' }
    
let dummy_loc_assertion a =
  { jc_assertion_loc = Loc.dummy_position; 
    jc_assertion_label = "";
    jc_assertion_node = a }




let create_static_var loc type_name fi =
  let ty = tr_type loc fi.java_field_info_type in
  let name = type_name ^ "_" ^ fi.java_field_info_name in
  let vi = Jc_pervasives.var ~static:true ty name in
  Hashtbl.add static_fields_table fi.java_field_info_tag vi;
  vi

(*s translation of structure types *)

let rec term_of_expr e = 
  let t =
    match e.java_expr_node with
      | JElit l -> JTlit l
      | JEvar vi -> JTvar vi
      | JEbin (e1, op, e2) -> 
	  JTbin (term_of_expr e1, Tint, op, term_of_expr e2)
      | JEun (op, e) -> JTun (Tint, op, term_of_expr e)
      | JEfield_access (e, fi) -> JTfield_access (term_of_expr e, fi)
      | JEstatic_field_access (ty, fi) -> JTstatic_field_access (ty, fi)
      | JEarray_access (e1, e2) ->
	  JTarray_access (term_of_expr e1, term_of_expr e2)
      | JEcast (t, e) -> JTcast (t, term_of_expr e)
      | _ -> assert false
  in
    { java_term_loc = e.java_expr_loc;
      java_term_type = e.java_expr_type;
      java_term_node = t }
      
(* exceptions *)

let tr_exception ei acc =
  JCexception_def(ei.jc_exception_info_name, ei) :: acc
  
(* array_length funs *)

let java_array_length_funs = Hashtbl.create 17

let java_array_length_fun st =
  try
    Hashtbl.find java_array_length_funs st.jc_struct_info_name 
  with
      Not_found -> assert false

let create_java_array_length_fun st =
  let fi = 
    Jc_pervasives.make_fun_info 
      ("java_array_length_" ^ st.jc_struct_info_name)
      Jc_pervasives.integer_type
  in
  Hashtbl.add java_array_length_funs st.jc_struct_info_name fi;
  fi

let array_types decls =
  Java_options.lprintf "(**********************)@.";
  Java_options.lprintf "(* array types        *)@.";
  Java_options.lprintf "(**********************)@.";
  Hashtbl.fold
    (fun t (s,f) (acc0, acc, decls) ->
       let st =
	 {
	   jc_struct_info_name = s;
	   jc_struct_info_parent = None;
	   jc_struct_info_root = object_root;
	   jc_struct_info_fields = [];
	   jc_struct_info_variant = Some object_variant;
	 }
       in
       let fi =
	 { jc_field_info_name = f;
	   jc_field_info_final_name = f;
	   jc_field_info_tag = 0 (* TODO *);
	   jc_field_info_type = tr_type Loc.dummy_position t;
	   jc_field_info_root = object_root;
	   jc_field_info_struct = st;
	   jc_field_info_rep = false;
	 }
       in
       st.jc_struct_info_fields <- [fi];
       Java_options.lprintf "%s@." st.jc_struct_info_name;
       Hashtbl.add array_struct_table t st;

       (* java_array_length fun *)
       let fi = create_java_array_length_fun st in
       let vi = Jc_pervasives.var 
	 (JCTpointer(st,Some num_zero,None)) "x" 
       in
       let result = Jc_pervasives.var Jc_pervasives.integer_type "\\result" in
       let vit = dummy_loc_term vi.jc_var_info_type (JCTvar vi) in
(*       let offset_mint = dummy_loc_term Jc_pervasives.integer_type 
	 (JCToffset (Offset_min, vit, st))
       in *)
       let offset_maxt = dummy_loc_term Jc_pervasives.integer_type 
	 (JCToffset (Offset_max, vit, st))
       in
       let spec =
	 { jc_fun_requires = (* \offset_max(x) >= -1 *)
	     dummy_loc_assertion 
	       (JCArelation (offset_maxt, Bge_int, minusonet));
	   jc_fun_free_requires = dummy_loc_assertion JCAtrue;
	   jc_fun_behavior = (* result == \offset_max(x)+1 *)
	     let result_var = 
	       dummy_loc_term vi.jc_var_info_type 
		 (JCTvar result)
	     in
	     [Loc.dummy_position,"non_null", 
	      { jc_behavior_assumes = None;
		jc_behavior_assigns = Some (Loc.dummy_position,[]);
		jc_behavior_ensures =
		  dummy_loc_assertion
		    (JCAand
		       [ dummy_loc_assertion
			   (JCArelation(result_var,
				    Beq_int,
				    dummy_loc_term vi.jc_var_info_type 
				      (term_plus_one
					 (dummy_loc_term vi.jc_var_info_type 
					    (JCToffset(Offset_max,vit,st))))));
			 dummy_loc_assertion
			   (JCArelation (result_var, Bge_int, term_zero)) ;
			 dummy_loc_assertion
			   (JCArelation (result_var,Blt_int, term_maxint))]);
		jc_behavior_throws = None } ] 
	     }
       in
	 (* non_null fun & pred *)
       let non_null_fi = create_non_null_fun st in
       let result = Jc_pervasives.var Jc_pervasives.boolean_type "\\result" in
       let offset_maxa = dummy_loc_assertion
	 (JCArelation (offset_maxt, Bge_int, minusonet)) in
       let non_null_spec =
	 { jc_fun_requires = dummy_loc_assertion JCAtrue;
	   jc_fun_free_requires = dummy_loc_assertion JCAtrue;
	   jc_fun_behavior = 
	     (* result ? \offset_min(x) == 0 && \offset_max(x) >= -1 : x = null *)
	     let resultt = dummy_loc_term vi.jc_var_info_type (JCTvar result) in
(*	     let offset_mina = dummy_loc_assertion
	       (JCArelation (offset_mint, Beq_int, zerot)) in *)
	     let non_null_ensuresa = 
	       dummy_loc_assertion
		 (JCAif
		    (resultt,
		     (* dummy_loc_assertion (JCAand [offset_mina;*) offset_maxa(*])*),
		     dummy_loc_assertion
		       (JCArelation (vit, Beq_pointer, nullt))))
	     in
	       [Loc.dummy_position, "normal",
		{ jc_behavior_assumes = None;
		  jc_behavior_assigns = None;
		  jc_behavior_ensures = non_null_ensuresa;
		  jc_behavior_throws = None }]
	 }
       in
       let non_null_pred = create_non_null_pred st in
	 (JClogic_fun_def (None, non_null_pred.jc_logic_info_name, [Jc_env.LabelHere],
			     [vi], JCAssertion offset_maxa) :: acc0,
	    JCstruct_def (st.jc_struct_info_name, Some "Object",
			st.jc_struct_info_fields, []) :: acc,
	  JCfun_def (fi.jc_fun_info_result.jc_var_info_type,
		     fi.jc_fun_info_name, [vi], spec, None) :: 
	    JCfun_def (non_null_fi.jc_fun_info_result.jc_var_info_type,
		       non_null_fi.jc_fun_info_name, [vi], non_null_spec, None) :: decls))
    Java_analysis.array_struct_table
	   ([], [
	      JCstruct_def("interface", None, [], []);
	      JCvariant_type_def("interface", [ "interface" ]);
	      JCvariant_type_def("Object", [ "Object" ]);
	    ], decls)
	   

(*****************

 locations

***************)

let rec location_set t =
  match t.java_term_node with
      | JTlit l -> assert false (* TODO *)
      | JTun(t,op,e1) -> assert false (* TODO *)
      | JTbin(e1,t,op,e2) -> assert false (* TODO *)
      | JTapp (_, _) -> assert false (* TODO *)
      | JTvar vi -> JCLSvar (get_var vi)
      | JTfield_access(t,fi) -> 
	  JCLSderef(location_set t,get_field fi,Jc_region.dummy_region)
      | JTstatic_field_access(ci,fi) ->
	  JCLSvar(get_static_var fi)
      | JTarray_length(t) -> assert false (* TODO *)
      | JTarray_access(t1,t2) -> 
	  begin
	    match t1.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct t1.java_term_loc ty in
		  let t1' = location_set t1 in
		  let t2' = term t2 in
		  let shift = JCLSrange(t1', Some t2', Some t2') in
		  JCLSderef(
		    shift,(List.hd st.jc_struct_info_fields),
		    Jc_region.dummy_region)
	      | _ -> assert false
	  end
      | JTarray_range(t1,t2,t3) -> 
	  begin
	    match t1.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct t1.java_term_loc ty in
		  let t1' = location_set t1 in
		  let t2' = term t2 in
		  let t3' = term t3 in
		  let shift = JCLSrange(t1', Some t2', Some t3') in
		  JCLSderef(
		    shift,(List.hd st.jc_struct_info_fields),
		    Jc_region.dummy_region)
	      | _ -> assert false
	  end
      | JTold t -> assert false (* TODO *)
      | JTat _ -> assert false (* TODO *)
      | JTcast(ty,t) -> assert false (* TODO *)


let location t =
  match t.java_term_node with
      | JTlit l -> assert false (* TODO *)
      | JTun(t,op,e1) -> assert false (* TODO *)
      | JTbin(e1,t,op,e2) -> assert false (* TODO *)
      | JTapp (_, _) -> assert false (* TODO *)
      | JTvar vi -> JCLvar (get_var vi)
      | JTfield_access(t,fi) -> 
	  JCLderef(location_set t,get_field fi,Jc_region.dummy_region)
      | JTstatic_field_access(ci,fi) ->
	  JCLvar(get_static_var fi)
      | JTarray_length(t) -> assert false (* TODO *)
      | JTarray_access(t1,t2) -> 
	  begin
	    match t1.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct t1.java_term_loc ty in
		  let t1' = location_set t1 in
		  let t2' = term t2 in
		  let shift = JCLSrange(t1', Some t2', Some t2') in
		  JCLderef(
		    shift,(List.hd st.jc_struct_info_fields),
		    Jc_region.dummy_region)
	      | _ -> assert false
	  end
      | JTarray_range(t1,t2,t3) -> 
	  begin
	    match t1.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct t1.java_term_loc ty in
		  let t1' = location_set t1 in
		  let t2' = term t2 in
		  let t3' = term t3 in
		  let shift = JCLSrange(t1', Some t2', Some t3') in
		  JCLderef(
		    shift,(List.hd st.jc_struct_info_fields),
		    Jc_region.dummy_region)
	      | _ -> assert false
	  end
      | JTold t -> assert false (* TODO *)
      | JTat _ -> assert false (* TODO *)
      | JTcast(ty,t) -> assert false (* TODO *)
  

let un_op op =
  match op with
    | Uminus -> Uminus_int
    | Ucompl -> Ubw_not
    | Unot -> Jc_ast.Unot
    | Uplus -> assert false (* TODO *)

let bin_op op =
  match op with
    | Badd -> Badd_int
    | Bmod -> Bmod_int
    | Bdiv -> Bdiv_int
    | Bmul -> Bmul_int
    | Bsub -> Bsub_int
    | Biff -> assert false
    | Bor -> Blor
    | Band -> Bland
    | Bimpl -> assert false 
    | Bgt -> Bgt_int
    | Bne -> Bneq_int
    | Beq -> Beq_int
    | Bge -> Bge_int
    | Ble -> Ble_int
    | Blt -> Blt_int
    | Basr -> Barith_shift_right
    | Blsr -> Blogical_shift_right
    | Blsl -> Bshift_left
    | Bbwxor -> Bbw_xor
    | Bbwor -> Bbw_or
    | Bbwand -> Bbw_and

let incr_op op =
  match op with
    | Preincr -> Prefix_inc
    | Predecr -> Prefix_dec
    | Postincr -> Postfix_inc
    | Postdecr -> Postfix_dec

let int_cast loc t e =
  if !Java_options.ignore_overflow || 
    match t with
      | JTYbase (Tinteger | Tint) -> false
      | _ -> true
  then e 
  else     
    JCTErange_cast(int_range, { jc_texpr_loc = loc;
				jc_texpr_type = Jc_pervasives.integer_type;
				jc_texpr_region = Jc_region.dummy_region;
				jc_texpr_label = "";
				jc_texpr_node = e })

let dummy_loc_expr ty e =
  { jc_texpr_loc = Loc.dummy_position; 
    jc_texpr_type = ty;
    jc_texpr_region = Jc_region.dummy_region;
    jc_texpr_label = "";
    jc_texpr_node = e }

let expr_one =
  dummy_loc_expr Jc_pervasives.integer_type 
    (JCTEconst (JCCinteger "1"))


let rec expr ?(reg=false) e =
  let reg = ref reg in
  let e' =
    match e.java_expr_node with
      | JElit l -> JCTEconst (lit l)
      | JEincr_local_var(op,v) -> 
	  reg := true;
	  JCTEincr_local(incr_op op,get_var v)
      | JEincr_field(op,e1,fi) -> 
	  reg := true;
	  JCTEincr_heap(incr_op op, expr e1, get_field fi)
      | JEincr_array (op, e1, e2) ->
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e1.java_expr_loc ty in
		  let e1' = expr e1 in
		  let shift = {
		    jc_texpr_loc = e.java_expr_loc;
		    jc_texpr_type = e1'.jc_texpr_type;
		    jc_texpr_region = Jc_region.dummy_region;
		    jc_texpr_label = e1'.jc_texpr_label;
		    jc_texpr_node = JCTEshift(e1', expr e2)
		  }
		  in
		  let fi = (List.hd st.jc_struct_info_fields) in
		  JCTEincr_heap (incr_op op, shift, fi)
	      | _ -> assert false
	  end
      | JEun (op, e1) -> 
	  let e1 = expr e1 in
	  reg := true;
	  int_cast e.java_expr_loc e.java_expr_type (JCTEunary(un_op op,e1))
      | JEbin (e1, op, e2) (* case e1 == null *)
	  when op = Beq && e2.java_expr_node = JElit Null ->
	  let e = expr e1 in
	    begin
	      match e1.java_expr_type with
		| JTYclass _ | JTYinterface _ -> 
		    let st = object_root in
		    JCTEunary (Jc_ast.Unot, 
			       dummy_loc_expr Jc_pervasives.boolean_type 
				 (JCTEcall (non_null_fun st, [e])))
		| JTYarray t ->
		    let st = get_array_struct e1.java_expr_loc t in
		      JCTEunary (Jc_ast.Unot, 
				 dummy_loc_expr Jc_pervasives.boolean_type 
				   (JCTEcall (non_null_fun st, [e])))
		| _ -> assert false
	    end
      | JEbin (e1, op, e2) (* case e1 != null *)
	  when op = Bne && e2.java_expr_node = JElit Null ->
	  let e = expr e1 in
	    begin
	      match e1.java_expr_type with
		| JTYclass _ | JTYinterface _ -> 
		    let st = object_root in
		    JCTEcall (non_null_fun st, [e])
		| JTYarray t ->
		    let st = get_array_struct e1.java_expr_loc t in
		      JCTEcall (non_null_fun st, [e])
		| _ -> assert false
	    end
      | JEbin (e1, op, e2) ->
	  let e1 = expr e1 and e2 = expr e2 in
	    reg := true;
	    int_cast e.java_expr_loc e.java_expr_type (JCTEbinary(e1,bin_op op,e2))
      | JEif (e1,e2,e3) -> 
	  JCTEif(expr e1, expr e2, expr e3)
      | JEvar vi -> JCTEvar (get_var vi)
      | JEstatic_field_access(ci,fi) ->
	  JCTEvar (get_static_var fi)
      | JEfield_access(e1,fi) -> 
	  reg := true;
	  JCTEderef(expr e1,get_field fi)
      | JEarray_length e -> 
	  begin
	    match e.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e.java_expr_loc ty in
		  reg := true;
		  JCTEcall (java_array_length_fun st, [expr e])
	      | _ -> assert false
	  end
      | JEarray_access(e1,e2) -> 
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e1.java_expr_loc ty in
		  let e1' = expr e1 in
		  let shift = {
		      jc_texpr_loc = e.java_expr_loc;
		      jc_texpr_type = e1'.jc_texpr_type;
		      jc_texpr_region = Jc_region.dummy_region;
		      jc_texpr_label = e1'.jc_texpr_label;
		      jc_texpr_node = JCTEshift(e1', expr e2)
		    }
		  in
		  reg := true;
		  JCTEderef(shift,(List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JEassign_local_var(vi,e) ->
	  JCTEassign_var(get_var vi,expr e)
      | JEassign_local_var_op(vi,op,e) ->
	  reg := true;
	  JCTEassign_var_op(get_var vi,bin_op op, expr e)
      | JEassign_field(e1,fi,e2) ->
	  reg := true;
	  JCTEassign_heap(expr e1,get_field fi,expr e2)
      | JEassign_field_op(e1,fi,op,e2) ->
	  reg := true;
	  JCTEassign_heap_op(expr e1,get_field fi,bin_op op,expr e2)
      | JEassign_static_field (fi, e) ->
	  JCTEassign_var (get_static_var fi, expr e)
      | JEassign_static_field_op (fi, op, e) ->
	  reg := true;
	  JCTEassign_var_op (get_static_var fi, bin_op op, expr e)
      | JEassign_array(e1,e2,e3) ->
	  reg := true;
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e1.java_expr_loc ty in
		  let e1' = expr e1 in
		  let shift = {
		      jc_texpr_loc = e.java_expr_loc;
		      jc_texpr_type = e1'.jc_texpr_type;
		      jc_texpr_region = Jc_region.dummy_region;
		      jc_texpr_label = e1'.jc_texpr_label;
		      jc_texpr_node = JCTEshift(e1', expr e2)
		    }
		  in
		  let fi = (List.hd st.jc_struct_info_fields) in
		  let e3' = expr e3 in
		  JCTEassign_heap(shift,fi,e3')
	      | _ -> assert false
	  end
      | JEassign_array_op(e1,e2,op,e3) ->
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e1.java_expr_loc ty in
		  let e1' = expr e1 in
		  let shift = {
		      jc_texpr_loc = e.java_expr_loc;
		      jc_texpr_type = e1'.jc_texpr_type;
		      jc_texpr_region = Jc_region.dummy_region;
		      jc_texpr_label = e1'.jc_texpr_label;
		      jc_texpr_node = JCTEshift(e1', expr e2)
		    }
		  in
		  let fi = (List.hd st.jc_struct_info_fields) in
		  let e3' = expr e3 in
		  JCTEassign_heap_op(shift,fi,bin_op op,e3')
	      | _ -> assert false
	  end
      | JEcall(e1,mi,args) -> 
	  reg := true;
	  JCTEcall (get_fun e.java_expr_loc mi.method_info_tag, List.map expr (e1 :: args))
      | JEconstr_call (e1, ci, args) -> 
	  reg := true;
	  JCTEcall (get_fun e.java_expr_loc ci.constr_info_tag, List.map expr (e1 :: args))
      | JEstatic_call(mi,args) -> 
	  reg := true;
	  JCTEcall(get_fun e.java_expr_loc mi.method_info_tag, List.map expr args)
      | JEnew_array(ty,[e1]) ->
	  let si = get_array_struct e.java_expr_loc ty in
	  JCTEalloc (expr e1, si) 
      | JEnew_array(ty,_) ->
	  assert false (* TODO *)
      | JEnew_object(ci,args) ->
	  let si = get_class ci.constr_info_class in
	  let ty = JCTpointer(si, Some num_zero, Some num_zero) in
	  let this = Jc_pervasives.var ~formal:true ty "this" in
	  let tt = Jc_pervasives.var ~formal:true Jc_pervasives.unit_type "tt" in
	  let args = (dummy_loc_expr ty (JCTEvar this)):: List.map expr args in
	  JCTElet(this,
		  dummy_loc_expr ty (JCTEalloc(expr_one, si)),
		  dummy_loc_expr ty
		    (JCTElet(tt,
			     dummy_loc_expr ty 
			       (JCTEcall(get_fun e.java_expr_loc 
					   ci.constr_info_tag,
					 args)),
			     dummy_loc_expr ty (JCTEvar this))))
      | JEcast(ty,e1) ->
	  begin
	    match ty with
	      | JTYbase t -> 
		  if !Java_options.ignore_overflow 
		  then 
		    (expr e1).jc_texpr_node
		  else
		    begin
		      reg := true;	    
		      JCTErange_cast(get_enum_info t, expr e1)
		    end
	      | JTYclass(_,ci) ->
		  let st = get_class ci in
		  reg := true;	    
		  JCTEcast(expr e1,st)
	      | JTYinterface ii -> 
		  begin
		    match e1.java_expr_type with
		      | JTYinterface _ ->
			  (expr e1).jc_texpr_node
		      | _ -> assert false (* TODO *)
(*
		  eprintf "Warning: cast to interface '%s' ignored.@."
		    ii.interface_info_name;
		    (expr e1).jc_texpr_node
*)
		  end
	      | JTYarray ty ->
		  let st = get_array_struct e.java_expr_loc ty in
		  reg := true;	    
		  JCTEcast(expr e1,st)		  
	      | JTYnull -> assert false 
	  end
      | JEinstanceof(e,ty) ->
	  begin
	    match ty with
	      | JTYclass(_,ci) ->
		  let st = get_class ci in
		  JCTEinstanceof(expr e,st)
	      | _ -> assert false (* TODO *)
	  end

  in { jc_texpr_loc = e.java_expr_loc ; 
       jc_texpr_type = tr_type e.java_expr_loc e.java_expr_type;
       jc_texpr_region = Jc_region.dummy_region;
       jc_texpr_label = if !reg then reg_loc e.java_expr_loc else "";
       jc_texpr_node = e' }

let initialiser e =
  match e with
    | JIexpr e -> expr ~reg:true e
    | _ -> assert false (* TODO *)

let dummy_loc_statement s =
  { jc_tstatement_loc = Loc.dummy_position; 
    jc_tstatement_node = s }

let make_block l =
  match l with
    | [s] -> s
    | _ -> dummy_loc_statement (JCTSblock l)

let reg_assertion a = 
  let a' = assertion ~reg:1 a  in
  let id = reg_loc a.java_assertion_loc in
(*
    Format.eprintf "adding loc '%s' on assertion@." id;
*)
    { a' with jc_assertion_label = id }

let reg_assertion_option a =
  match a with
    | None -> dummy_loc_assertion JCAtrue 
    | Some a -> reg_assertion a

let loop_annot inv dec =
  { jc_loop_tag = get_loop_counter ();
    jc_loop_invariant = reg_assertion inv;
    jc_loop_variant = 
      Option_misc.map 
	(fun t -> 
	   let t' = term t in
	   { t' with jc_term_label = reg_loc t.java_term_loc }) dec 
  }


let rec statement s =
  let s' =
    match s.java_statement_node with
      | JSskip -> JCTSblock []
      | JSbreak None -> JCTSbreak { label_info_name = ""; times_used = 0 }
      | JSbreak (Some l) -> JCTSbreak { label_info_name = l ; times_used = 0 }
      | JSreturn_void -> JCTSreturn_void
      | JSreturn e -> 
	  JCTSreturn (tr_type e.java_expr_loc e.java_expr_type,expr e)
      | JSthrow e -> JCTSthrow(get_exception e.java_expr_type,Some (expr e))
      | JSblock l -> JCTSblock (List.map statement l)	  
      | JSvar_decl (vi, init, s) -> 
	  let vi = create_var s.java_statement_loc vi in
	  JCTSdecl(vi, Option_misc.map initialiser init, statement s)
      | JSif (e, s1, s2) ->
	  JCTSif (expr e, statement s1, statement s2)
      | JSwhile(e,inv,dec,s) ->
	  let la = loop_annot inv dec in
	  JCTSwhile("", expr e, la, statement s)
      | JSfor (el1, e, inv, dec, el2, body) ->
	  let exprl = 
	    List.map
	      (fun e -> 
		 let e = expr e in
		 { jc_tstatement_loc = e.jc_texpr_loc ;
		   jc_tstatement_node = JCTSexpr e })
	      el1
	  in
	  let la = loop_annot inv dec in
	  let res =
	    { jc_tstatement_loc = s.java_statement_loc ;
	      jc_tstatement_node = 
		JCTSfor ("", expr e, List.map expr el2, la, statement body) }
	  in JCTSblock (exprl @ [res])
      | JSfor_decl(decls,e,inv,dec,sl,body) ->
	  let decls = List.map
	    (fun (vi,init) -> 
	       (create_var s.java_statement_loc vi, Option_misc.map initialiser init))
	    decls
	  in
	  let la = loop_annot inv dec in
	  let res =
	    List.fold_right
	      (fun (vi,init) acc -> 
		 { jc_tstatement_loc = acc.jc_tstatement_loc ;
		   jc_tstatement_node = JCTSdecl(vi,init, acc) })
	      decls
	      { jc_tstatement_loc = s.java_statement_loc ;
		jc_tstatement_node = 
		  JCTSfor("", expr e, List.map expr sl, la, statement body) }
	  in JCTSblock [res]
      | JSexpr e -> JCTSexpr (expr e)
      | JSassert(id,e) -> 
	  let name =
	    match id with
	      | None -> reg_loc e.java_assertion_loc
	      | Some id -> reg_loc ~id e.java_assertion_loc
	  in
	  let e' = reg_assertion e in
	  JCTSassert((*Some name,*) { e' with jc_assertion_label = name } )
      | JSswitch(e,l) -> 
	  JCTSswitch(expr e,List.map switch_case l)
      | JStry(s1, catches, finally) ->
	  JCTStry(block s1,
		  List.map 
		    (fun (vi,s2) ->
		       let e = get_exception vi.java_var_info_type in
		       let vti = create_var s.java_statement_loc vi in
		       (e, Some vti, block s2))
		    catches,
		  make_block 
		    (Option_misc.fold (fun s acc -> List.map statement s) finally []))

  in { jc_tstatement_loc = s.java_statement_loc ; jc_tstatement_node = s' }

and statements l = List.map statement l

and block l = make_block (statements l)

and switch_case (labels,b) =
  (List.map switch_label labels, statements b)

and switch_label = function
  | Java_ast.Default -> None
  | Java_ast.Case e -> Some (expr e)

let behavior (id,assumes,throws,assigns,ensures) =
  (fst id,snd id,
  { jc_behavior_assumes = Option_misc.map assertion assumes;
    jc_behavior_assigns = 
      Option_misc.map 
	(fun (loc,a) -> (loc,List.map location a)) assigns ;
    jc_behavior_ensures = reg_assertion ensures;
    jc_behavior_throws = 
      Option_misc.map (fun ci -> get_exception (JTYclass(false,ci))) throws;
  })


let tr_method mi req behs b acc =
  let params = List.map (create_var Loc.dummy_position) mi.method_info_parameters in
  let params =
    match mi.method_info_has_this with
      | None -> params
      | Some vi -> 
	  (create_var Loc.dummy_position vi) :: params
  in
  let t = match mi.method_info_result with
    | None -> None
    | Some vi ->
	let _nvi = create_var Loc.dummy_position vi in 
	Some vi.java_var_info_type
  in
  let nfi = 
    create_fun Loc.dummy_position 
      mi.method_info_tag mi.method_info_result 
      mi.method_info_trans_name mi.method_info_parameters
  in
  let body = Option_misc.map statements b in
  let _ = 
    reg_loc ~id:nfi.jc_fun_info_name 
      ~name:("Method "^mi.method_info_name)
      mi.method_info_loc 
  in
  JCfun_def(tr_type_option Loc.dummy_position t,
	    nfi.jc_fun_info_name,
	    params,
	    { jc_fun_requires = reg_assertion_option req;
	      jc_fun_free_requires = dummy_loc_assertion JCAtrue;
	      jc_fun_behavior = List.map behavior behs},
	    body)::acc
	  
let tr_constr ci req behs b acc =
  let params = 
    List.map (create_var Loc.dummy_position) ci.constr_info_parameters 
  in
  let this =
    match ci.constr_info_this with
      | None -> assert false
      | Some vi -> (create_var Loc.dummy_position vi) 
  in
(*
  let _result =
    match ci.constr_info_result with
      | None -> assert false
      | Some vi -> (create_var Loc.dummy_position vi) 
  in
*)
  let nfi = 
    create_fun Loc.dummy_position ci.constr_info_tag None
      ci.constr_info_trans_name ci.constr_info_parameters
  in
  let body = statements b
(*
@ 
    [dummy_loc_statement (JCTSreturn(this.jc_var_info_type,
				     dummy_loc_expr 
				       this.jc_var_info_type
				       (JCTEvar this)))] 
*)
  in
(* NO: TODO 
  let body = 
    dummy_loc_statement (JCTSdecl(this,None,make_block body))
  in
  *)
  let body = match body with
    | [] -> None
    | _ -> Some [make_block body]
  in
  let _ = 
    reg_loc ~id:nfi.jc_fun_info_name 
      ~name:("Constructor of class "^ci.constr_info_class.class_info_name)
      ci.constr_info_loc 
  in
  JCfun_def(Jc_pervasives.unit_type,
	    nfi.jc_fun_info_name,
	    this :: params,
	    { jc_fun_requires = reg_assertion_option req;
	      jc_fun_free_requires = dummy_loc_assertion JCAtrue;
	      jc_fun_behavior = List.map behavior behs}, 
	    body)::acc
	  
(*s axioms *)

let tr_axiom id is_axiom lab p acc =
  JClemma_def(id,is_axiom,List.map tr_logic_label lab,assertion p)::acc


let tr_logic_fun fi b acc =   
  let nfi = create_logic_fun Loc.dummy_position fi in
  match b with
    | Java_typing.JAssertion a ->
	JClogic_fun_def(nfi.jc_logic_info_result_type,
			nfi.jc_logic_info_name,
			nfi.jc_logic_info_labels,
			nfi.jc_logic_info_parameters,
			JCAssertion(assertion a))::acc
    | Java_typing.JTerm t -> 
	JClogic_fun_def(nfi.jc_logic_info_result_type,
			nfi.jc_logic_info_name,
			nfi.jc_logic_info_labels,
			nfi.jc_logic_info_parameters,
			JCTerm(term t))::acc
    | Java_typing.JReads l ->
	JClogic_fun_def(nfi.jc_logic_info_result_type,
			nfi.jc_logic_info_name,
			nfi.jc_logic_info_labels,
			nfi.jc_logic_info_parameters,
			JCReads(List.map location l))::acc

let tr_field type_name acc fi =
  let vi = create_static_var Loc.dummy_position type_name fi in
    if fi.java_field_info_is_final then
      let vi_ty = vi.jc_var_info_type in
      let logic_body, axiom_body =
	try
	  let e = 
	    Hashtbl.find Java_typing.field_initializer_table fi.java_field_info_tag
	  in
	  let values =
	    Hashtbl.find Java_typing.final_field_values_table fi.java_field_info_tag
	  in
	  let get_value value = match fi.java_field_info_type with
	    | JTYarray (JTYbase t) | JTYbase t -> 
		begin match t with
		  | Tshort | Tbyte | Tchar | Tint 
		    | Tlong | Tdouble | Tinteger -> 
		      JCCinteger (Num.string_of_num value)
		  | Tboolean -> assert false (* TODO *)
		  | Tfloat | Treal -> assert false (* TODO *) 
		  | Tunit -> assert false
		end
	    | JTYnull | JTYclass _ | JTYinterface _ | JTYarray _ -> 
		assert false
	  in
	    match e with
	      | None -> JCReads [], None
	      | Some (JIexpr e) ->
		  assert (List.length values = 1);
		  (* evaluated constant expressions are translated *)
		  JCTerm (
		    { (term (term_of_expr e)) with 
			jc_term_node = JCTconst (get_value (List.hd values)) }),
		  None
	      | Some (JIlist il) ->
		  let n = List.length il in
		    assert (List.length values = n);
		    let si = match vi_ty with
		      | JCTpointer (si, _, _) -> si
		      | _ -> assert false
		    in
		    let vit = dummy_loc_term vi_ty (JCTvar vi) in
		    let a =
		      let app = {
			jc_app_fun = non_null_pred si.jc_struct_info_name;
			jc_app_args = [vit];
			jc_app_region_assoc = [];
			jc_app_label_assoc = [] ;
		      } in
			dummy_loc_assertion (JCAapp app)
		    in
		    let a =
		      make_and [a;
			dummy_loc_assertion 
			   (JCArelation (
			      dummy_loc_term Jc_pervasives.integer_type 
				(JCToffset (Offset_max, vit, si)),
			      Beq_int, 
			      dummy_loc_term Jc_pervasives.integer_type 
				(JCTconst (JCCinteger (string_of_int (n - 1))))))]
		    in
		    let beq = match fi.java_field_info_type with
		      | JTYarray jt -> 
			  begin match jt with
			    | JTYbase (Tshort | Tbyte | Tchar | Tint 
			      | Tlong | Tdouble | Tinteger) -> Beq_int
			    | JTYbase Tboolean -> Beq_bool 
			    | JTYbase (Tfloat | Treal) -> Beq_real 
			    | JTYbase Tunit | JTYnull -> assert false 
			    | JTYclass _ | JTYinterface _ | JTYarray _ -> Beq_pointer
			  end
		      | JTYbase _ | JTYnull | JTYclass _ | JTYinterface _ -> 
			  assert false
		    in
		    let fi' = List.hd si.jc_struct_info_fields in 
		    let a, _ =
		      List.fold_left2
			(fun (acc, cpt) init n -> 
			   match init with
			     | JIexpr e ->
				 let t = term (term_of_expr e) in
				 make_and
				   [acc;
				    dummy_loc_assertion 
				      (JCArelation (
					 dummy_loc_term fi'.jc_field_info_type 
					   (JCTderef 
					      (dummy_loc_term t.jc_term_type
						 (JCTshift 
						    (vit, dummy_loc_term 
						       Jc_pervasives.integer_type
						       (JCTconst (JCCinteger 
								    (string_of_int cpt))))),
					       Jc_env.LabelHere,
					       fi')),
					 beq,
					 { t with jc_term_node = 
					     JCTconst (get_value n) }))], 
				 cpt + 1
			     | JIlist _ -> assert false (* TODO / Not supported *))
			(a, 0) il values
		    in
		      JCReads [], Some a
	with Not_found -> 
	  Java_options.lprintf "Warning: final field '%s' of %a has no known value@."
	    fi.java_field_info_name 
	    Java_typing.print_type_name 
	    fi.java_field_info_class_or_interface;
	  JCReads [], None
      in
      let decl =
	JClogic_fun_def 
	  (Some vi_ty, vi.jc_var_info_final_name, [], [], logic_body)
      in
      let decl = match axiom_body with
	| None -> [decl]
	| Some a -> 
	    [JClemma_def (fi.java_field_info_name ^ "_values", 
			  true, [Jc_env.LabelHere], a); 
	     decl]
      in
	decl @ acc      
    else
      let e = 
	try
	  match Hashtbl.find Java_typing.field_initializer_table 
	    fi.java_field_info_tag with
	      | None -> None
	      | Some e -> Some (initialiser e)
	with Not_found -> None
      in
	JCvar_def(vi.jc_var_info_type,vi.jc_var_info_final_name,e)::acc
	  
	  
(* class *)

let tr_class ci acc0 acc =
  let (static_fields, fields) = 
    List.partition 
      (fun fi -> fi.java_field_info_is_static)
      ci.class_info_fields
  in
  let super =
    let superclass = Option_misc.map (fun ci -> ci.class_info_name)
      ci.class_info_extends in
      match superclass with 
	| None -> if ci.class_info_name = "Object" then None else Some "Object"
	| _ -> superclass
  in
  let acc = List.fold_left (tr_field ci.class_info_name) acc static_fields in
    (* create exceptions if subclass of Exception *)
    begin
      if ci.class_info_is_exception then
	ignore (create_exception 
		  (Some (tr_type Loc.dummy_position (JTYclass (false, ci))))
		  ci.class_info_name);
    end;
    let fields = List.map (create_field Loc.dummy_position) fields in
      (* non_null fun & pred *)
    let si = get_class ci in
    let acc = 
      if ci.class_info_name = "Object" then
	let non_null_fi = create_non_null_fun si in
	let vi = Jc_pervasives.var (JCTpointer (si, Some num_zero, None)) "x" in
	let result = Jc_pervasives.var Jc_pervasives.boolean_type "\\result" in
	let vit = dummy_loc_term vi.jc_var_info_type (JCTvar vi) in
	let offset_maxt = dummy_loc_term Jc_pervasives.integer_type
	  (JCToffset (Offset_max, vit, si)) in
	let offset_maxa = dummy_loc_assertion
	  (JCArelation (offset_maxt, Beq_int, zerot)) in
	let non_null_spec =
	  { jc_fun_requires = dummy_loc_assertion JCAtrue;
	    jc_fun_free_requires = dummy_loc_assertion JCAtrue;
	    jc_fun_behavior = 
	      (* result ? \offset_min(x) == 0 && \offset_max(x) == 0 : x = null *)
	      let resultt = dummy_loc_term vi.jc_var_info_type (JCTvar result) in
(*	      let offset_mint = dummy_loc_term Jc_pervasives.integer_type 
		(JCToffset (Offset_min, vit, si)) in*)
(*	      let offset_mina = dummy_loc_assertion
		(JCArelation (offset_mint, Beq_int, zerot)) in *)
		[Loc.dummy_position, "normal",
		 { jc_behavior_assumes = None;
		   jc_behavior_assigns = None;
 		   jc_behavior_ensures =
		     dummy_loc_assertion
		       (JCAif
			 (resultt,
			  (* dummy_loc_assertion (JCAand [offset_mina;*) offset_maxa(*])*),
			  dummy_loc_assertion
			    (JCArelation (vit, Beq_pointer, nullt))));
		   jc_behavior_throws = None }] 
	  }
	in
	let non_null_pred = create_non_null_pred si in
	  JCfun_def (Jc_pervasives.boolean_type,
		     non_null_fi.jc_fun_info_name, [vi], non_null_spec, None) ::
	    JClogic_fun_def (None, non_null_pred.jc_logic_info_name, [Jc_env.LabelHere],
			     [vi], JCAssertion offset_maxa) :: acc
      else acc
    in
      JCstruct_def (ci.class_info_name, super, fields, []) :: acc0, acc
      

(* interfaces *)

let tr_interface ii acc = 
  let fields = ii.interface_info_fields in
  let acc = List.fold_left (tr_field ii.interface_info_name) acc fields in
    acc

let tr_class_or_interface ti acc0 acc =
  match ti with
    | TypeClass ci -> 
	Java_options.lprintf "Creating JC structure for class '%s'@." ci.class_info_name;
	tr_class ci acc0 acc
    | TypeInterface ii -> 
	Java_options.lprintf "Handling interface '%s'@." ii.interface_info_name;
	(acc0, tr_interface ii acc)

let tr_invariants ci id invs decls =
  let invs =
    List.map
      (fun ((_, s), a) -> 
	 let vi = create_var Loc.dummy_position id in
	   s, vi, assertion a)
      invs
  in
    List.map
      (fun d -> 
	 match d with
	   | JCstruct_def (s, so, fil, []) when s = ci.class_info_name ->
	       JCstruct_def (s, so, fil, invs)
	   | _ -> d)
      decls



(* static invariants *)

let tr_static_invariant (s, a) = 
  JCglobinv_def (s, assertion a)


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/krakatoa.byte"
End: 
*)

