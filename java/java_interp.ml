
open Format
open Jc_output
open Jc_env
open Jc_fenv
open Jc_ast
open Java_env
open Java_ast
open Java_tast
open Java_pervasives

(*s locs table *)



type kind =
  | ArithOverflow
  | DownCast
  | IndexBounds
  | PointerDeref
  | UserCall
  | DivByZero
  | Pack
  | Unpack


let locs_table : (string, (kind option * Loc.position)) Hashtbl.t 
    = Hashtbl.create 97
let name_counter = ref 0
let reg_loc ?name ?kind loc =
  let id = match name with
    | None ->  
	incr name_counter;
	"K_" ^ string_of_int !name_counter
    | Some n -> n
  in
  Java_options.lprintf "recording location for id '%s'@." id;
  Hashtbl.add locs_table id (kind,loc);
  id

let print_kind fmt k =
  fprintf fmt "%s"
    (match k with
       | Pack -> "Pack"
       | Unpack -> "Unpack"
       | DivByZero -> "DivByZero"
       | UserCall -> "UserCall"
       | PointerDeref -> "PointerDeref"
       | IndexBounds -> "IndexBounds"
       | DownCast -> "DownCast"
       | ArithOverflow -> "ArithOverflow"
    )

let abs_fname f =
  if Filename.is_relative f then
    Filename.concat (Unix.getcwd ()) f 
  else f

let print_locs fmt =
  Hashtbl.iter 
    (fun id (k,(b,e)) ->
       fprintf fmt "[%s]@\n" id;
       begin
	 match k with
	   | None -> ()
	   | Some k -> fprintf fmt "kind = %a@\n" print_kind k
       end;
       fprintf fmt "file = \"%s\"@\n" (abs_fname b.Lexing.pos_fname);
       let l = b.Lexing.pos_lnum in
       let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
       let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
       fprintf fmt "line = %d@\n" l;
       fprintf fmt "begin = %d@\n" fc;
       fprintf fmt "end = %d@\n@\n" lc)
    locs_table

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
  if Java_options.ignore_overflow then acc else
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
	if Java_options.ignore_overflow then Jc_pervasives.integer_type else
	short_type
    | Tint -> 
	if Java_options.ignore_overflow then Jc_pervasives.integer_type else
	int_type
    | Tlong -> 
	if Java_options.ignore_overflow then Jc_pervasives.integer_type else
	long_type
    | Tchar -> 
	if Java_options.ignore_overflow then Jc_pervasives.integer_type else
	char_type
    | Tbyte  -> 
	if Java_options.ignore_overflow then Jc_pervasives.integer_type else
	byte_type
    | Treal -> Jc_pervasives.real_type
    | Tfloat -> assert false (* TODO *)
    | Tdouble -> assert false (* TODO *)

(*s class types *)

let get_class ci =
  {
    jc_struct_info_name = ci.class_info_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = ci.class_info_name;
    jc_struct_info_fields = [];
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

let st_interface = 
  {
    jc_struct_info_name = "interface";
    jc_struct_info_parent = None;
    jc_struct_info_root = "interface";
    jc_struct_info_fields = [];
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
    | JTYclass(non_null,ci) -> 
	let st = get_class ci in
	JCTpointer(st,Some num_zero,
	           if non_null then Some num_zero else None)
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
	  vi.java_var_info_name
	  Loc.report_position vi.java_var_info_decl_loc
	;
	raise Not_found

let create_var ?(formal=false) loc vi =
  let ty = tr_type loc vi.java_var_info_type in
  let nvi = Jc_pervasives.var ~formal ty vi.java_var_info_name in
  nvi.jc_var_info_assigned <- vi.java_var_info_assigned;
  Hashtbl.add vi_table vi.java_var_info_tag nvi;
  nvi

(*s logic funs *)

let logics_table = Hashtbl.create 97

let get_logic_fun fi =
  try
    Hashtbl.find logics_table fi.java_logic_info_tag
  with
      Not_found -> assert false

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

let dummy_loc_term ty t =
  { jc_term_loc = Loc.dummy_position; 
    jc_term_type = ty;
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
	  JCTapp(get_logic_fun fi,List.map term el)
      | JTvar vi -> JCTvar (get_var vi)
      | JTfield_access(t,fi) -> JCTderef(term t,get_field fi)
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
		      jc_term_type = t1'.jc_term_type;
		      jc_term_node = JCTshift(t1', term t2)
		    }
		  in
		  JCTderef(shift,(List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JTarray_range _ -> assert false
      | JTold t -> JCTold(term t)
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
       jc_term_type = tr_type  t.java_term_loc t.java_term_type ;
       jc_term_node = t' }

let quantifier = function
  | Forall -> Jc_ast.Forall
  | Exists -> Jc_ast.Exists

let rec assertion a =
  let lab = ref "" in
  let a' =
    match a.java_assertion_node with
      | JAtrue -> JCAtrue
      | JAfalse -> JCAfalse
      | JAnot a -> JCAnot(assertion a)
      | JAbin(e1,t,op,e2) -> JCArelation(term e1, lbin_op t op, term e2)
      | JAbin_obj(e1,op,e2) -> JCArelation(term e1, lobj_op op, term e2)
      | JAapp (fi, el)-> 
	  JCAapp(get_logic_fun fi,List.map term el)
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
	  JCAand [assertion a1 ; assertion a2]
      | JAbool_expr t -> JCAbool_term(term t)
      | JAinstanceof (t, ty) ->
	  let ty = tr_type Loc.dummy_position ty in
	    match ty with
	      | JCTpointer (si, _, _) ->
		  JCAinstanceof (term t, si)
	      | _ -> assert false

  in { jc_assertion_loc = a.java_assertion_loc ; 
       jc_assertion_label = !lab;
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
    (fun t (s,f) (acc,decls) ->
       let st =
	 {
	   jc_struct_info_name = s;
	   jc_struct_info_parent = None;
	   jc_struct_info_root = "Object";
	   jc_struct_info_fields = [];
	 }
       in
       let fi =
	 { jc_field_info_name = f;
	   jc_field_info_final_name = f;
	   jc_field_info_tag = 0 (* TODO *);
	   jc_field_info_type = tr_type Loc.dummy_position t;
	   jc_field_info_root = s;
	   jc_field_info_struct = st;
	   jc_field_info_rep = false;
	 }
       in
       st.jc_struct_info_fields <- [fi];
       Java_options.lprintf "%s@." st.jc_struct_info_name;
       Hashtbl.add array_struct_table t st;
       let fi = create_java_array_length_fun st in
       let vi = Jc_pervasives.var 
	 (JCTpointer(st,Some num_zero,None)) "x" 
       in
       let result = Jc_pervasives.var Jc_pervasives.integer_type "\\result" in
       let nvi = dummy_loc_term vi.jc_var_info_type (JCTvar vi) in
       let spec =
	 { jc_fun_requires = (* x!=null *)
	     dummy_loc_assertion 
	       (JCArelation(nvi,Bneq_pointer,
			    dummy_loc_term JCTnull (JCTconst JCCnull)));
	   jc_fun_behavior = (* result == \offset_max(x)+1 *)
	     let result_var = 
	       dummy_loc_term vi.jc_var_info_type 
		 (JCTvar result)
	     in
	     ["non_null", 
	      { jc_behavior_assumes = None;
		jc_behavior_assigns = Some [];
		jc_behavior_ensures =
		  dummy_loc_assertion
		    (JCAand
		       [ dummy_loc_assertion
			   (JCArelation(result_var,
				    Beq_int,
				    dummy_loc_term vi.jc_var_info_type 
				      (term_plus_one
					 (dummy_loc_term vi.jc_var_info_type 
					    (JCToffset(Offset_max,nvi,st))))));
			 dummy_loc_assertion
			   (JCArelation(result_var,Bge_int,term_zero)) ;
			 dummy_loc_assertion
			   (JCArelation(result_var,Blt_int,term_maxint))]);
		jc_behavior_throws = None } ] 
	     }
       in
	 (JCstruct_def (st.jc_struct_info_name, Some "Object",
			st.jc_struct_info_fields, []) :: acc,
	  JCfun_def(fi.jc_fun_info_return_type,
		  fi.jc_fun_info_name,[vi],spec,None) :: decls))
    Java_analysis.array_struct_table
    ([JCstruct_def("interface", None, [], [])],decls)
      

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
      | JTfield_access(t,fi) -> JCLSderef(location_set t,get_field fi)
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
		  JCLSderef(shift,(List.hd st.jc_struct_info_fields))
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
		  JCLSderef(shift,(List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JTold t -> assert false (* TODO *)
      | JTcast(ty,t) -> assert false (* TODO *)


let location t =
  match t.java_term_node with
      | JTlit l -> assert false (* TODO *)
      | JTun(t,op,e1) -> assert false (* TODO *)
      | JTbin(e1,t,op,e2) -> assert false (* TODO *)
      | JTapp (_, _) -> assert false (* TODO *)
      | JTvar vi -> JCLvar (get_var vi)
      | JTfield_access(t,fi) -> JCLderef(location_set t,get_field fi)
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
		  JCLderef(shift,(List.hd st.jc_struct_info_fields))
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
		  JCLderef(shift,(List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JTold t -> assert false (* TODO *)
      | JTcast(ty,t) -> assert false (* TODO *)
  

let behavior (id,assumes,throws,assigns,ensures) =
  (snd id,
  { jc_behavior_assumes = Option_misc.map assertion assumes;
    jc_behavior_assigns = Option_misc.map (List.map location) assigns ;
    jc_behavior_ensures = assertion ensures;
    jc_behavior_throws = 
      Option_misc.map (fun ci -> get_exception (JTYclass(false,ci))) throws;
  })

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
  if Java_options.ignore_overflow || 
    match t with
      | JTYbase Tint -> false
      | _ -> true
  then e 
  else     
    JCTErange_cast(int_range, { jc_texpr_loc = loc;
				jc_texpr_type = Jc_pervasives.integer_type;
				jc_texpr_label = "";
				jc_texpr_node = e })

let dummy_loc_expr ty e =
  { jc_texpr_loc = Loc.dummy_position; 
    jc_texpr_type = ty;
    jc_texpr_label = "";
    jc_texpr_node = e }


let rec expr e =
  let lab = ref "" in
  let e' =
    match e.java_expr_node with
      | JElit l -> JCTEconst (lit l)
      | JEincr_local_var(op,v) -> 
	  JCTEincr_local(incr_op op,get_var v)
      | JEincr_field(op,e,fi) -> 
	  JCTEincr_heap(incr_op op, expr e, get_field fi)
      | JEincr_array (op, e1, e2) ->
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e1.java_expr_loc ty in
		  let e1' = expr e1 in
		  let shift = {
		    jc_texpr_loc = e.java_expr_loc;
		    jc_texpr_type = e1'.jc_texpr_type;
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
	  lab := reg_loc e.java_expr_loc;
	  int_cast e.java_expr_loc e.java_expr_type (JCTEunary(un_op op,e1))
      | JEbin (e1, op, e2) -> 
	  let e1 = expr e1 and e2 = expr e2 in
	  lab := reg_loc e.java_expr_loc;
	  int_cast e.java_expr_loc e.java_expr_type (JCTEbinary(e1,bin_op op,e2))
      | JEif (e1,e2,e3) -> 
	  JCTEif(expr e1, expr e2, expr e3)
      | JEvar vi -> JCTEvar (get_var vi)
      | JEstatic_field_access(ci,fi) ->
	  JCTEvar (get_static_var fi)
      | JEfield_access(e1,fi) -> 
	  JCTEderef(expr e1,get_field fi)
      | JEarray_length(e) -> 
	  begin
	    match e.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e.java_expr_loc ty in
		  JCTEcall(java_array_length_fun st,[expr e])
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
		      jc_texpr_label = e1'.jc_texpr_label;
		      jc_texpr_node = JCTEshift(e1', expr e2)
		    }
		  in
		  JCTEderef(shift,(List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JEassign_local_var(vi,e) ->
	  JCTEassign_var(get_var vi,expr e)
      | JEassign_local_var_op(vi,op,e) ->
	  JCTEassign_var_op(get_var vi,bin_op op, expr e)
      | JEassign_field(e1,fi,e2) ->
	  JCTEassign_heap(expr e1,get_field fi,expr e2)
      | JEassign_field_op(e1,fi,op,e2) ->
	  JCTEassign_heap_op(expr e1,get_field fi,bin_op op,expr e2)
      | JEassign_static_field (fi, e) ->
	  JCTEassign_var (get_static_var fi, expr e)
      | JEassign_static_field_op (fi, op, e) ->
	  JCTEassign_var_op (get_static_var fi, bin_op op, expr e)
      | JEassign_array(e1,e2,e3) ->
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct e1.java_expr_loc ty in
		  let e1' = expr e1 in
		  let shift = {
		      jc_texpr_loc = e.java_expr_loc;
		      jc_texpr_type = e1'.jc_texpr_type;
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
	  lab := reg_loc e.java_expr_loc;
	  JCTEcall (get_fun e.java_expr_loc mi.method_info_tag, List.map expr (e1 :: args))
      | JEconstr_call (e1, ci, args) -> 
	  lab := reg_loc e.java_expr_loc;
	  JCTEcall (get_fun e.java_expr_loc ci.constr_info_tag, List.map expr (e1 :: args))
      | JEstatic_call(mi,args) -> 
	  lab := reg_loc e.java_expr_loc;
	  JCTEcall(get_fun e.java_expr_loc mi.method_info_tag, List.map expr args)
      | JEnew_array(ty,[e1]) ->
	  let si = get_array_struct e.java_expr_loc ty in
	  JCTEalloc (expr e1, si) 
      | JEnew_array(ty,_) ->
	  assert false (* TODO *)
      | JEnew_object(ci,args) ->
	  let si = get_class ci.constr_info_class in
	  JCTEalloc (dummy_loc_expr int_type (JCTEconst (JCCinteger "1")), si) 
      | JEcast(ty,e1) ->
	  begin
	    match ty with
	      | JTYbase t -> 
		  if Java_options.ignore_overflow 
		  then 
		    (expr e1).jc_texpr_node
		  else
		    JCTErange_cast(get_enum_info t, expr e1)
	      | JTYclass(_,ci) ->
		  let st = get_class ci in
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
       jc_texpr_label = !lab;
       jc_texpr_node = e' }

let initialiser e =
  match e with
    | JIexpr e -> expr e
    | _ -> assert false (* TODO *)

let dummy_loc_statement s =
  { jc_tstatement_loc = Loc.dummy_position; 
    jc_tstatement_node = s }

let make_block l =
  match l with
    | [s] -> s
    | _ -> dummy_loc_statement (JCTSblock l)

let rec statement s =
  let s' =
    match s.java_statement_node with
      | JSskip -> JCTSblock []
      | JSbreak None -> JCTSbreak ""
      | JSbreak (Some l) -> JCTSbreak l
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
	  let inv' = assertion inv in
	  let la =
	    { jc_loop_tag = get_loop_counter ();
	      jc_loop_invariant = 
		{ inv' with 
		    jc_assertion_label = reg_loc inv.java_assertion_loc };
	      jc_loop_variant = Option_misc.map term dec }
	  in
	  JCTSwhile(expr e, la, statement s)
      | JSfor (el1, e, inv, dec, el2, body) ->
	  let exprl = 
	    List.map
	      (fun e -> 
		 let e = expr e in
		 { jc_tstatement_loc = e.jc_texpr_loc ;
		   jc_tstatement_node = JCTSexpr e })
	      el1
	  in
	  let la =
	    { jc_loop_tag = get_loop_counter ();
	      jc_loop_invariant = assertion inv;
	      jc_loop_variant = Option_misc.map term dec }
	  in
	  let res =
	    { jc_tstatement_loc = s.java_statement_loc ;
	      jc_tstatement_node = 
		JCTSfor (expr e, List.map expr el2, la, statement body) }
	  in JCTSblock (exprl @ [res])
      | JSfor_decl(decls,e,inv,dec,sl,body) ->
	  let decls = List.map
	    (fun (vi,init) -> 
	       (create_var s.java_statement_loc vi, Option_misc.map initialiser init))
	    decls
	  in
	  let la =
	    { jc_loop_tag = get_loop_counter ();
	      jc_loop_invariant = assertion inv;
	      jc_loop_variant = Option_misc.map term dec }
	  in
	  let res =
	    List.fold_right
	      (fun (vi,init) acc -> 
		 { jc_tstatement_loc = acc.jc_tstatement_loc ;
		   jc_tstatement_node = JCTSdecl(vi,init, acc) })
	      decls
	      { jc_tstatement_loc = s.java_statement_loc ;
		jc_tstatement_node = 
		  JCTSfor(expr e, List.map expr sl, la, statement body) }
	  in JCTSblock [res]
      | JSexpr e -> JCTSexpr (expr e)
      | JSassert(id,e) -> 
	  let name =
	    match id with
	      | None -> reg_loc e.java_assertion_loc
	      | Some id -> reg_loc ~name:id e.java_assertion_loc
	  in
	  JCTSassert(Some name, assertion e)
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

let reg_assertion_option a =
  match a with
    | None -> dummy_loc_assertion JCAtrue 
    | Some a -> 
	let a' = assertion a in
	let id = reg_loc a.java_assertion_loc in
	Format.eprintf "adding loc '%s' on pre-condition@." id;
	{ a' with jc_assertion_label = id }

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
  JCfun_def(tr_type_option Loc.dummy_position t,
	    nfi.jc_fun_info_name,
	    params,
	    { jc_fun_requires = reg_assertion_option req;
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
  JCfun_def(Jc_pervasives.unit_type,
	    nfi.jc_fun_info_name,
	    this :: params,
	    { jc_fun_requires = reg_assertion_option req;
	      jc_fun_behavior = List.map behavior behs},
	    Some [make_block body])::acc
	  
(*s axioms *)

let tr_axiom id p acc =
  JCaxiom_def(id,assertion p)::acc


let tr_logic_fun fi b acc =   
  let nfi = create_logic_fun Loc.dummy_position fi in
  match b with
    | Java_typing.JAssertion a ->
	JClogic_fun_def(nfi.jc_logic_info_result_type,
			nfi.jc_logic_info_name,
			nfi.jc_logic_info_parameters,
			JCAssertion(assertion a))::acc
    | Java_typing.JTerm t -> 
	JClogic_fun_def(nfi.jc_logic_info_result_type,
			nfi.jc_logic_info_name,
			nfi.jc_logic_info_parameters,
			JCTerm(term t))::acc
    | Java_typing.JReads l ->
	JClogic_fun_def(nfi.jc_logic_info_result_type,
			nfi.jc_logic_info_name,
			nfi.jc_logic_info_parameters,
			JCReads(List.map location l))::acc

let tr_field type_name acc fi =
  let vi = create_static_var Loc.dummy_position type_name fi in
  if fi.java_field_info_is_final then
    let body =
      try
	let e = 
	  Hashtbl.find Java_typing.field_initializer_table fi.java_field_info_tag
	in
	let values =
	  Hashtbl.find Java_typing.final_field_values_table fi.java_field_info_tag
	in
	match e with
	  | None -> JCReads []
	  | Some (JIexpr e) -> (* JCTerm (term (term_of_expr e)) *)
	      (* evaluated constant expressions are translated (Nicolas) *)
	      assert (List.length values = 1);
	      JCTerm (
		{ (term (term_of_expr e)) 
		  with jc_term_node = 
		    (JCTconst (JCCinteger (Num.string_of_num (List.hd values)))) })
	  | Some (JIlist _) -> raise Not_found (* TODO: with axioms ? (Nicolas) *)
      with Not_found -> 
	Java_options.lprintf "Warning: final field '%s' of %a has no known value@."
	  fi.java_field_info_name 
	  Java_typing.print_type_name 
	  fi.java_field_info_class_or_interface;
	JCReads []
    in
    let decl =
      JClogic_fun_def(Some vi.jc_var_info_type, vi.jc_var_info_name,
		      [], body)
    in
    decl::acc      
  else
    let e = 
      try
	match Hashtbl.find Java_typing.field_initializer_table 
	  fi.java_field_info_tag with
	    | None -> None
	    | Some e -> Some (initialiser e)
      with Not_found -> None
    in
    JCvar_def(vi.jc_var_info_type,vi.jc_var_info_name,e)::acc


let tr_class ci acc0 acc =
  let (static_fields, fields) = 
    List.partition 
      (fun fi -> fi.java_field_info_is_static)
      ci.class_info_fields
  in
  let super =
    Option_misc.map (fun ci -> ci.class_info_name) ci.class_info_extends
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
      JCstruct_def 
	(ci.class_info_name, super, fields, []) :: acc0, acc
      
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

