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
open Cil_types
open Cil
open Cilutil
open Ast_info
open Extlib
open Visitor

(* Utility functions *)
open Format

let constant_expr ?(loc=Cil_datatype.Location.unknown) e = 
  Ast_info.constant_expr ~loc e

exception NotImplemented of string
exception Unsupported of string

let fatal fmt = Jessie_options.fatal ~current:true fmt

let notimplemented fmt =
  Jessie_options.with_failure
    (fun evt -> raise (NotImplemented evt.Log.evt_message)) ~current:true fmt

let unsupported fmt =
  Jessie_options.with_failure
    (fun evt ->
       raise (Unsupported evt.Log.evt_message)
    ) ~current:true fmt

let warning fmt = Jessie_options.warning ~current:true fmt
let warn_general fmt = Jessie_options.warning ~current:false fmt

let warn_once =
  let known_warns = Hashtbl.create 7 in
  fun s ->
    if not (Hashtbl.mem known_warns s) then begin
      Hashtbl.add known_warns s ();
      warn_general "%s" s
    end

(*****************************************************************************)
(* Options                                                                   *)
(*****************************************************************************)

let flatten_multi_dim_array = ref false


(*****************************************************************************)
(* Source locations                                                         *)
(*****************************************************************************)

let is_unknown_location loc =
  (fst loc).Lexing.pos_lnum = 0


(*****************************************************************************)
(* Types                                                                     *)
(*****************************************************************************)

(* type for ghost variables until integer is a valid type for ghosts *)
let almost_integer_type = TInt(ILongLong,[])

let struct_type_for_void = ref voidType

(* Query functions on types *)

let rec app_term_type f default = function
  | Ctype typ -> f typ
  | Ltype ({lt_name = "set"},[t]) -> app_term_type f default t
  | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> default

let rec force_app_term_type f = function
  | Ctype typ -> f typ
  | Ltype ({ lt_name = "set"},[t]) -> force_app_term_type f t
  | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ as ty ->
      Jessie_options.fatal "Unexpected non-C type %a" !Ast_printer.d_logic_type ty

let get_unique_field ty = match unrollType ty with
  | TComp(compinfo,_,_) ->
      begin match compinfo.cfields with
	| [content_fi] -> content_fi
	| _ ->
	    Jessie_options.fatal "Type %a has no unique field" !Ast_printer.d_type ty
      end
  | _ -> Jessie_options.fatal "non-struct (unique field)"

let get_struct_name = function
  | TComp(compinfo,_,_) -> compinfo.cname
  | _ -> Jessie_options.fatal "non-struct (name)"

let get_struct_info = function
  | TComp(compinfo,_,_) -> compinfo
  | _ -> Jessie_options.fatal "non-struct (info)"

(* Integral types *)

let size_in_bytes ik =
  let size = function
    | IBool -> assert false
    | IChar | ISChar | IUChar -> 1 (* Cil assumes char is one byte *)
    | IInt | IUInt -> theMachine.theMachine.sizeof_int
    | IShort | IUShort -> theMachine.theMachine.sizeof_short
    | ILong | IULong -> theMachine.theMachine.sizeof_long
    | ILongLong | IULongLong -> theMachine.theMachine.sizeof_longlong
  in
  size ik

let integral_type_size_in_bytes ty =
  match unrollType ty with
  | TInt(IBool,_attr) -> (* TODO *)
    Extlib.not_yet_implemented "Common.integral_type_size_in_bytes IBool"
  | TInt(ik,_attr) -> size_in_bytes ik
  | TEnum ({ekind = IBool},_) -> 
    Extlib.not_yet_implemented "Common.integral_type_size_in_bytes IBool"
  | TEnum (ei,_) -> size_in_bytes ei.ekind
  | _ -> assert false

let integral_type_size_in_bits ty =
  integral_type_size_in_bytes ty * 8

let min_value_of_integral_type ?bitsize ty =
  let min_of signed size_in_bytes =
    let numbits =
      match bitsize with Some siz -> siz | None -> size_in_bytes * 8
    in
    if signed then
      My_bigint.neg
	(My_bigint.power_int_positive_int 2
	  (numbits - 1))
    else My_bigint.zero
  in
  match unrollType ty with
    | TInt(IBool,_attr) -> My_bigint.zero
    | TInt(ik,_attr) ->
	min_of (isSigned ik) (size_in_bytes ik)
    | TEnum ({ ekind = IBool},_) -> My_bigint.zero
    | TEnum ({ekind=ik},_) ->
	min_of (isSigned ik) (size_in_bytes ik)
    | _ -> assert false

let max_value_of_integral_type ?bitsize ty =
  let max_of signed size_in_bytes =
    let numbits =
      match bitsize with Some siz -> siz | None -> size_in_bytes * 8
    in
    if signed then
      My_bigint.pred
	(My_bigint.power_int_positive_int 2
	  (numbits - 1))
    else
      My_bigint.pred
	(My_bigint.power_int_positive_int 2
	  numbits)
  in
  match unrollType ty with
    | TInt(IBool,_attr) -> My_bigint.one
    | TInt(ik,_attr) ->
	max_of (isSigned ik) (size_in_bytes ik)
    | TEnum ({ekind=IBool},_) -> My_bigint.one
    | TEnum ({ekind=ik},_) -> max_of (isSigned ik) (size_in_bytes ik)
    | _ -> assert false

let all_integral_types = Hashtbl.create 5

let name_of_integral_type ?bitsize ty =
  let name_it signed size_in_bytes =
    let numbits =
      match bitsize with Some siz -> siz | None -> size_in_bytes * 8
    in
    let name = (if signed then "" else "u") ^ "int" ^ (string_of_int numbits) in
    Hashtbl.replace all_integral_types name (ty,numbits);
    name
  in
  match unrollType ty with
    | TInt(IBool,_attr) -> "_bool"
    | TInt(ik,_attr) ->
	name_it (isSigned ik) (size_in_bytes ik)
    | TEnum ({ekind= IBool},_) -> "_bool"
    | TEnum ({ekind = ik},_) -> name_it (isSigned ik) (size_in_bytes ik)
    | _ -> assert false

(* Reference type *)

(* We introduce a reference type, that is different from the C pointer or
 * array type. It is a direct translation in C of the Jessie bounded pointer
 * type, where the lower/upper bounds that can be safely accessed are
 * statically known. To avoid introducing a new type, we reuse the existing
 * C pointer type, with an attribute "arrlen" to give the size.
 * Then, we use it as a regular pointer type. E.g., we allow dynamic allocation
 * of such references:
 *     r = (TRef(T)) (malloc (sizeof(T)));
 * and usual dereference:
 *     T t = *r;
 * Another advantage is it should be working fine with [typeOf], [typeOfLval],
 * [pointed_type] and similar functions.
 *
 * As a result of this transformation, all allocation/releases of memory
 * on a reference type do implicitly allocate/release the fields of reference
 * type. It will be translated in Jessie in various alloc/free statements.
 *)

let arraylen_attr_name = "arraylen"

let mkTRef elemty _msg =
  (* Define the same arguments as for [mkTRefArray] *)
(*
  Format.eprintf "mkTRef, coming from %s@." msg;
*)
  let size = constant_expr My_bigint.one and attr = [] in
  (* Do the same as in [mkTRefArray] *)
  let siz = expToAttrParam size in
  let attr = addAttribute (Attr(arraylen_attr_name,[siz])) attr in
  (* Avoid creating an array for single pointed elements that do not
   * originate in a C array, to avoid having to access to the first
   * element everywhere.
   *)
  TPtr(elemty,attr)

let mkTRefArray (elemty,size,attr) =
  (* Check the array size is of a correct form *)
  ignore (lenOfArray64 (Some size));
  let siz = expToAttrParam size in
  let attr = addAttribute (Attr(arraylen_attr_name,[siz])) attr in
  (* Make the underlying type an array so that indexing it is still valid C. *)
  TPtr(TArray(elemty,Some size,empty_size_cache (),[]),attr)

let reference_size ty =
  match findAttribute arraylen_attr_name (typeAttrs ty) with
    | [AInt i] -> 
(*
        eprintf "AInt has argument %d@." i;
*)
        Int64.of_int i
    | _ -> assert false

let is_reference_type ty =
  isPointerType ty && hasAttribute arraylen_attr_name (typeAttrs ty)

let is_array_reference_type ty =
  is_reference_type ty && isArrayType (direct_pointed_type ty)

let reference_of_array ty =
  let rec reftype ty =
    if isArrayType ty then
      let elty = reftype (direct_element_type ty) in
(*       if array_size ty > 0L then *)
	let size = constant_expr (direct_array_size ty) in
	mkTRefArray(elty,size,[])
(*       else *)
(* 	(\* Array of zero size, e.g. in struct array hack. *\) *)
(* 	TPtr(elty,[]) *)
    else ty
  in
  assert (isArrayType ty);
  reftype ty

(* Wrappers on [mkCompInfo] that update size/offset of fields *)

let mkStructEmpty stname =
  mkCompInfo true stname (fun _ -> []) []

let mkStructSingleton ?(padding=0) stname finame fitype =
  let compinfo =
    mkCompInfo true stname
      (fun _ -> [finame,fitype,None,[],CurrentLoc.get ()]) []
  in
  let fi = get_unique_field (TComp(compinfo,empty_size_cache (),[])) in
  fi.fsize_in_bits <- Some (bitsSizeOf fitype);
  fi.foffset_in_bits <- Some 0;
  fi.fpadding_in_bits <- Some padding;
  compinfo

(* Locally use 64 bits integers *)
open Integer

let bits_sizeof ty =
  let rec rec_size ?(top_size=false) ty =
    match unrollType ty with
      | TPtr _ ->
	  if is_reference_type ty && not top_size then
	    rec_size (pointed_type ty) * (reference_size ty)
	  else
	    Int64.of_int (bitsSizeOf ty)
      | TArray _ -> assert false (* Removed by translation *)
      | TFun _ -> unsupported "Function pointer type %a not allowed" !Ast_printer.d_type ty
      | TNamed _ -> assert false (* Removed by call to [unrollType] *)
      | TComp(compinfo,_,_) ->
	  let size_from_field fi =
	    match
	      fi.foffset_in_bits, fi.fsize_in_bits, fi.fpadding_in_bits
	    with
	      | Some off, Some siz, Some padd ->
		  Int64.of_int off + Int64.of_int siz + Int64.of_int padd
	      | _ -> assert false
	  in
	  if compinfo.cstruct then
	    match List.rev compinfo.cfields with
	      | [] -> 0L
	      | fi :: _ -> size_from_field fi
	  else
	    List.fold_left max 0L (List.map size_from_field compinfo.cfields)
      | TEnum _ | TVoid _ | TInt _ | TFloat _ | TBuiltin_va_list _ ->
	  Int64.of_int (bitsSizeOf ty)
  in
  rec_size ~top_size:true ty

(* Come back to normal 31 bits integers *)
open Pervasives


(*****************************************************************************)
(* Names                                                                     *)
(*****************************************************************************)

(* Predefined entities *)

let name_of_valid_string = "valid_string"
let name_of_valid_wstring = "valid_wstring"
let name_of_strlen = "strlen"
let name_of_wcslen = "wcslen"
let name_of_assert = "assert"
let name_of_free = "free"
let name_of_malloc = "malloc"
let name_of_calloc = "calloc"
let name_of_realloc = "realloc"

let predefined_name =
  [ (* coding functions *)
    name_of_assert;
    name_of_malloc;
    name_of_calloc;
    name_of_realloc;
    name_of_free;
  ]

let is_predefined_name s = List.mem s predefined_name

let is_assert_function v = isFunctionType v.vtype && v.vname = name_of_assert
let is_free_function v = isFunctionType v.vtype && v.vname = name_of_free
let is_malloc_function v = isFunctionType v.vtype && v.vname = name_of_malloc
let is_calloc_function v = isFunctionType v.vtype && v.vname = name_of_calloc
let is_realloc_function v = isFunctionType v.vtype && v.vname = name_of_realloc

(* Name management *)

let unique_name_generator is_exception =
  let unique_names = Hashtbl.create 127 in
  let rec aux s =
    if is_exception s then s else
      try
	let s = if s = "" then "unnamed" else s in
	let count = Hashtbl.find unique_names s in
	let s = s ^ "_" ^ (string_of_int !count) in
	if Hashtbl.mem unique_names s then
	  aux s
	else
	  (Hashtbl.add unique_names s (ref 0);
	   incr count; s)
      with Not_found ->
	Hashtbl.add unique_names s (ref 0); s
  in
  let add s = Hashtbl.add unique_names s (ref 0) in
  aux, add

let unique_name, add_unique_name =
(*  let u = *)unique_name_generator is_predefined_name
(* in (fun s -> let s' = u s in s') *)

let unique_logic_name, add_unique_logic_name =
(*  let u = *) unique_name_generator (fun _ -> false)
(* in (fun s -> let s' = u s in s')*)

let unique_name_if_empty s =
  if s = "" then unique_name "unnamed" else s

(* Jessie reserved names *)

let jessie_reserved_names =
  [
    (* a *) "and"; "as"; "assert"; "assigns"; "assumes"; "axiom";
    (* b *) "behavior"; "boolean"; "break";
    (* c *) "case"; "catch"; "continue";
    (* d *) "default"; "do";
    (* e *) "else"; "end"; "ensures"; "exception";
    (* f *) "false"; "finally"; "for"; "free";
    (* g *) "goto";
    (* i *) "if"; "in"; "integer"; "invariant";
    (* l *) "lemma"; "let"; "logic";
    (* m *) "match";
    (* n *) "new"; "null";
    (* o *) "of";
    (* p *) "pack";
    (* r *) "reads"; "real"; "rep"; "requires"; "return";
    (* s *) "switch";
    (* t *) "tag"; "then"; "throw"; "throws"; "true"; "try"; "type";
    (* u *) "unit"; "unpack";
    (* v *) "var"; "variant";
    (* w *) "while"; "with";
  ]

let () = List.iter add_unique_name jessie_reserved_names
let () = List.iter add_unique_logic_name jessie_reserved_names

(*
let reserved_name name =
  if List.mem name jessie_reserved_names then name else unique_name name

let reserved_logic_name name =
  if List.mem name jessie_reserved_names then name else unique_logic_name name
*)

(* Type name *)

let string_explode s =
  let rec next acc i =
    if i >= 0 then next (s.[i] :: acc) (i-1) else acc
  in
  next [] (String.length s - 1)

let string_implode ls =
  let s = String.create (List.length ls) in
  ignore (List.fold_left (fun i c -> s.[i] <- c; i + 1) 0 ls);
  s

let filter_alphanumeric s assoc default =
  let is_alphanum c =
    String.contains "abcdefghijklmnopqrstuvwxyz" c
    || String.contains "ABCDEFGHIJKLMNOPQRSTUVWXYZ" c
    || String.contains "123456789" c
    || c = '_'
  in
  let alphanum_or_default c =
    if is_alphanum c then c
    else try List.assoc c assoc with Not_found -> default
  in
  string_implode (List.map alphanum_or_default (string_explode s))

let type_name ty =
  ignore (flush_str_formatter ());
  fprintf str_formatter "%a" !Ast_printer.d_type ty;
  let name = flush_str_formatter () in
  filter_alphanumeric name [('*','x')] '_'

let logic_type_name ty =
  ignore (flush_str_formatter ());
  let old_mode = Kernel.Unicode.get() in
  Kernel.Unicode.set false;
  fprintf str_formatter "%a" !Ast_printer.d_logic_type ty;
  let name = flush_str_formatter () in
  Kernel.Unicode.set old_mode;
  filter_alphanumeric name [('*','x')] '_'

let name_of_padding_type = (*reserved_logic_name*) "padding"

let name_of_string_declspec = "valid_string"

let name_of_hint_assertion = "hint"

let name_of_safety_behavior = "safety"

let name_of_default_behavior = "default"

(*****************************************************************************)
(* Visitors                                                                  *)
(*****************************************************************************)

(* Visitor for adding globals and global initializations (for global
 * variables). It delays updates to the file until after the visitor has
 * completed its work, to avoid visiting a newly created global or
 * initialization.
 *)

let attach_detach_mode = ref false
let globinits : stmt list ref = ref []
let globals : global list ref = ref []
let globactions : (unit -> unit) list ref = ref []

(*
let attach_globinit init =
  assert (!attach_detach_mode);
  globinits := init :: !globinits
*)

let attach_global g =
  assert (!attach_detach_mode);
  globals := g :: !globals

let attach_globaction action =
  assert (!attach_detach_mode);
  globactions := action :: !globactions

(*
let detach_globinits file =
  let gif =
    Kernel_function.get_definition (Globals.Functions.get_glob_init file)
  in
  Format.eprintf "Common.detach_globinits: len(globinits) = %d@."
    (List.length !globinits);
  gif.sbody.bstmts <- List.rev_append !globinits gif.sbody.bstmts;
  globinits := []
*)

let detach_globals file =
  file.globals <- !globals @ file.globals;
  List.iter
    (function GVar(v,init,_) -> Globals.Vars.add v init | _ -> ()) !globals;
  globals := []

let detach_globactions () =
  List.iter (fun f -> f ()) !globactions;
  globactions := []

let do_and_update_globals action file =
  attach_detach_mode := true;
  assert (!globinits = [] && !globals = [] && !globactions = []);
  action file;
 (*
 detach_globinits file;
 *)
  detach_globals file;
  detach_globactions ();
  attach_detach_mode := false

let visit_and_update_globals visitor file =
  do_and_update_globals (visitFramacFile visitor) file

(* Visitor for adding statements in front of the body *)

let adding_statement_mode = ref false
let pending_statements_at_beginning : stmt list ref = ref []
let pending_statements_at_end : stmt list ref = ref []

let add_pending_statement ~beginning s =
  assert (!adding_statement_mode);
  if beginning then
    pending_statements_at_beginning := s :: !pending_statements_at_beginning
  else
    pending_statements_at_end := s :: !pending_statements_at_end

let insert_pending_statements f =
  f.sbody.bstmts <-
    List.rev_append !pending_statements_at_beginning f.sbody.bstmts;
  pending_statements_at_beginning := [];
  match !pending_statements_at_end with [] -> () | slist ->
    (* Insert pending statements before return statement *)
    let return_stat =
      Kernel_function.find_return (Globals.Functions.get f.svar)
    in
    (* Remove labels from the single return statement. Leave them on the most
     * external block with cleanup code instead.
     *)
    let s = { return_stat with labels = []; } in
    let block = mkBlock (List.rev_append (s :: slist) []) in
    return_stat.skind <- Block block;
    pending_statements_at_end := []

class proxy_frama_c_visitor (visitor : Visitor.frama_c_visitor) =
object
  (* [VP 2011-08-24] Do not inherit from Visitor.frama_c_visitor: all methods
     that are not overloaded have to come from visitor. Otherwise, proxy will
     fail to delegate some of its actions. *)

  method set_current_kf kf = visitor#set_current_kf kf

  method set_current_func f = visitor#set_current_func f

  method current_kf = visitor#current_kf

  method current_func = visitor#current_func

  method push_stmt s = visitor#push_stmt s
  method pop_stmt s = visitor#pop_stmt s

  method current_stmt = visitor#current_stmt
  method current_kinstr = visitor#current_kinstr

  method get_filling_actions = visitor#get_filling_actions
  method fill_global_tables = visitor#fill_global_tables

  method vlogic_label = visitor#vlogic_label

  (* Modify visitor on functions so that it prepends/postpends statements *)
  method vfunc f =
    adding_statement_mode := true;
    assert (!pending_statements_at_beginning = []);
    assert (!pending_statements_at_end = []);
    let change c = fun f -> adding_statement_mode:=false; c f in
    match visitor#vfunc f with
      | SkipChildren -> ChangeToPost(f, change (fun x -> x))
      | JustCopy -> JustCopyPost (change (fun x -> x))
      | JustCopyPost f -> JustCopyPost (change f)
      | ChangeTo f' -> ChangeToPost (f', change (fun x -> x))
      | ChangeToPost(f',action) -> ChangeToPost(f', change action)
      | DoChildren ->
	  let postaction_func f =
	    insert_pending_statements f;
	    adding_statement_mode := false;
	    f
	  in
	  ChangeDoChildrenPost (f, postaction_func)
      | ChangeDoChildrenPost (f', action) ->
	  let postaction_func f =
	    let f = action f in
	    insert_pending_statements f;
	    adding_statement_mode := false;
	    f
	  in
	  ChangeDoChildrenPost (f', postaction_func)

  (* Inherit all other visitors *)

  (* Methods introduced by the Frama-C visitor *)
  method vfile = visitor#vfile
  method vrooted_code_annotation = visitor#vrooted_code_annotation
  method vglob_aux = visitor#vglob_aux
  method vstmt_aux = visitor#vstmt_aux

  (* Methods from Cil visitor for coding constructs *)
  method vblock = visitor#vblock
  method vvrbl = visitor#vvrbl
  method vvdec = visitor#vvdec
  method vexpr = visitor#vexpr
  method vlval = visitor#vlval
  method voffs = visitor#voffs
  method vinitoffs = visitor#vinitoffs
  method vinst = visitor#vinst
  method vinit = visitor#vinit
  method vtype = visitor#vtype
  method vattr = visitor#vattr
  method vattrparam = visitor#vattrparam

  (* Methods from Cil visitor for logic constructs *)
  method vlogic_type = visitor#vlogic_type
  method vterm = visitor#vterm
  method vterm_node = visitor#vterm_node
  method vterm_lval = visitor#vterm_lval
  method vterm_lhost = visitor#vterm_lhost
  method vterm_offset = visitor#vterm_offset
  method vlogic_info_decl = visitor#vlogic_info_decl
  method vlogic_info_use = visitor#vlogic_info_use
  method vlogic_var_decl = visitor#vlogic_var_decl
  method vlogic_var_use = visitor#vlogic_var_use
  method vquantifiers = visitor#vquantifiers
  method vpredicate = visitor#vpredicate
  method vpredicate_named = visitor#vpredicate_named
(*
  method vpredicate_info_decl = visitor#vpredicate_info_decl
  method vpredicate_info_use = visitor#vpredicate_info_use
*)
  method vbehavior = visitor#vbehavior
  method vspec = visitor#vspec
  method vassigns = visitor#vassigns
  method vloop_pragma = visitor#vloop_pragma
  method vslice_pragma = visitor#vslice_pragma
  method vdeps = visitor#vdeps
  method vcode_annot = visitor#vcode_annot
  method vannotation = visitor#vannotation

  method behavior = visitor#behavior
  method project = visitor#project
  method frama_c_plain_copy = visitor#frama_c_plain_copy
  method is_annot_before = visitor#is_annot_before
  method plain_copy_visitor = visitor#plain_copy_visitor
  method queueInstr = visitor#queueInstr
  method reset_current_func = visitor#reset_current_func
  method reset_current_kf = visitor#reset_current_kf
  method unqueueInstr = visitor#unqueueInstr
  method vcompinfo = visitor#vcompinfo
  method venuminfo = visitor#venuminfo
  method venumitem = visitor#venumitem
  method vfieldinfo = visitor#vfieldinfo
  method vfrom = visitor#vfrom
  method vglob = visitor#vglob
  method vimpact_pragma = visitor#vimpact_pragma
  method vlogic_ctor_info_decl = visitor#vlogic_ctor_info_decl
  method vlogic_ctor_info_use = visitor#vlogic_ctor_info_use
  method vlogic_type_def = visitor#vlogic_type_def
  method vlogic_type_info_decl = visitor#vlogic_type_info_decl
  method vlogic_type_info_use = visitor#vlogic_type_info_use
  method vstmt = visitor#vstmt

  method vallocates = visitor#vallocates
  method vallocation = visitor#vallocation
  method vfrees = visitor#vfrees

end

let visit_and_push_statements_visitor visitor =
  new proxy_frama_c_visitor visitor

let visit_and_push_statements visit visitor file =
  let visitor = new proxy_frama_c_visitor visitor in
  visit visitor file

(* Visitor for tracing computation *)

class trace_frama_c_visitor (visitor : Visitor.frama_c_visitor) =
object

  inherit Visitor.generic_frama_c_visitor
    (Project.current ()) (Cil.inplace_visit ()) as super

  (* Inherit all visitors, printing visited item on the way *)

  (* Methods introduced by the Frama-C visitor *)
  method vfile = visitor#vfile
  method vrooted_code_annotation = visitor#vrooted_code_annotation
  method vglob_aux g =
    Jessie_options.feedback "%a" !Ast_printer.d_global g;
    visitor#vglob_aux g
  method vstmt_aux s =
    Jessie_options.feedback "%a" !Ast_printer.d_stmt s;
    visitor#vstmt_aux s

  (* Methods from Cil visitor for coding constructs *)
  method vfunc = visitor#vfunc
  method vblock b =
    Jessie_options.feedback "%a" !Ast_printer.d_block b;
    visitor#vblock b
  method vvrbl v =
    Jessie_options.feedback "%s" v.vname;
    visitor#vvrbl v
  method vvdec v =
    Jessie_options.feedback "%s" v.vname;
    visitor#vvdec v
  method vexpr e =
    Jessie_options.feedback "%a" !Ast_printer.d_exp e;
    visitor#vexpr e
  method vlval lv =
    Jessie_options.feedback "%a" !Ast_printer.d_lval lv;
    visitor#vlval lv
  method voffs off =
    Jessie_options.feedback "%a" !Ast_printer.d_offset off;
    visitor#voffs off
  method vinitoffs off =
    Jessie_options.feedback "%a" !Ast_printer.d_offset off;
    visitor#vinitoffs off
  method vinst i =
    Jessie_options.feedback "%a" !Ast_printer.d_instr i;
    visitor#vinst i
  method vinit = visitor#vinit
  method vtype ty =
    Jessie_options.feedback "%a" !Ast_printer.d_type ty;
    visitor#vtype ty
  method vattr attr =
    Jessie_options.feedback "%a" !Ast_printer.d_attr attr;
    visitor#vattr attr
  method vattrparam pattr =
    Jessie_options.feedback "%a" !Ast_printer.d_attrparam pattr;
    visitor#vattrparam pattr

  (* Methods from Cil visitor for logic constructs *)
  method vlogic_type lty =
    Jessie_options.feedback "%a" !Ast_printer.d_logic_type lty;
    visitor#vlogic_type lty
  method vterm t =
    Jessie_options.feedback "%a" !Ast_printer.d_term t;
    visitor#vterm t
  method vterm_node = visitor#vterm_node
  method vterm_lval tlv =
    Jessie_options.feedback "%a" !Ast_printer.d_term_lval tlv;
    visitor#vterm_lval tlv
  method vterm_lhost = visitor#vterm_lhost
  method vterm_offset = visitor#vterm_offset
  method vlogic_info_decl = visitor#vlogic_info_decl
  method vlogic_info_use = visitor#vlogic_info_use
  method vlogic_var_decl lv =
    Jessie_options.feedback "%a" !Ast_printer.d_logic_var lv;
    visitor#vlogic_var_decl lv
  method vlogic_var_use lv =
    Jessie_options.feedback "%a" !Ast_printer.d_logic_var lv;
    visitor#vlogic_var_use lv
  method vquantifiers = visitor#vquantifiers
  method vpredicate = visitor#vpredicate
  method vpredicate_named p =
    Jessie_options.feedback "%a" !Ast_printer.d_predicate_named p;
    visitor#vpredicate_named p
(*
  method vpredicate_info_decl = visitor#vpredicate_info_decl
  method vpredicate_info_use = visitor#vpredicate_info_use
*)
  method vbehavior = visitor#vbehavior
  method vspec funspec =
    Jessie_options.feedback "%a" !Ast_printer.d_funspec funspec;
    visitor#vspec funspec
  method vassigns = visitor#vassigns
  method vloop_pragma = visitor#vloop_pragma
  method vslice_pragma = visitor#vslice_pragma
  method vdeps = visitor#vdeps
  method vcode_annot annot =
    Jessie_options.feedback "%a" !Ast_printer.d_code_annotation annot;
    visitor#vcode_annot annot
  method vannotation annot =
    Jessie_options.feedback "%a" !Ast_printer.d_annotation annot;
    visitor#vannotation annot

end

let visit_and_trace_framac visit visitor file =
  let visitor = new trace_frama_c_visitor visitor in
  visit visitor file

let visit_and_trace_cil visit visitor file =
  let visitor = new trace_frama_c_visitor visitor in
  visit (visitor :> cilVisitor) file

(* Visitor for fixpoint computation *)

let change = ref false

let signal_change () = change := true

let visit_until_convergence visitor file =
  change := true;
  while !change do
    change := false;
    visitFramacFile visitor file;
  done

(* Visitor methods for sharing preaction/postaction between exp/term/tsets *)

let do_on_term_offset (preaction_offset,postaction_offset) tlv =
  let preaction_toffset tlv =
    match preaction_offset with None -> tlv | Some preaction_offset ->
      let lv,env =
	!Db.Properties.Interp.force_term_offset_to_offset tlv
      in
      let lv = preaction_offset lv in
      !Db.Properties.Interp.force_back_offset_to_term_offset env lv
  in
  let postaction_toffset tlv =
    match postaction_offset with None -> tlv | Some postaction_offset ->
      let lv,env = !Db.Properties.Interp.force_term_offset_to_offset tlv in
      let lv = postaction_offset lv in
      !Db.Properties.Interp.force_back_offset_to_term_offset env lv
  in
  ChangeDoChildrenPost (preaction_toffset tlv, postaction_toffset)

let do_on_term_lval (preaction_lval,postaction_lval) tlv =
  let preaction_tlval tlv =
    match preaction_lval with None -> tlv | Some preaction_lval ->
      let lv,env = !Db.Properties.Interp.force_term_lval_to_lval tlv in
      let lv = preaction_lval lv in
      !Db.Properties.Interp.force_back_lval_to_term_lval env lv
  in
  let postaction_tlval tlv =
    match postaction_lval with None -> tlv | Some postaction_lval ->
      let lv,env = !Db.Properties.Interp.force_term_lval_to_lval tlv in
      let lv = postaction_lval lv in
      !Db.Properties.Interp.force_back_lval_to_term_lval env lv
  in
  ChangeDoChildrenPost (preaction_tlval tlv, postaction_tlval)

let do_on_term (preaction_expr,postaction_expr) t =
  let preaction_term t =
    match preaction_expr with None -> t | Some preaction_expr ->
      let e,env = !Db.Properties.Interp.force_term_to_exp t in
      let e = map_under_info preaction_expr e in
      !Db.Properties.Interp.force_back_exp_to_term env e
  in
  let postaction_term t =
    match postaction_expr with None -> t | Some postaction_expr ->
      let e,env = !Db.Properties.Interp.force_term_to_exp t in
      let e = map_under_info postaction_expr e in
      !Db.Properties.Interp.force_back_exp_to_term env e
  in
  ChangeDoChildrenPost (preaction_term t, postaction_term)

(*****************************************************************************)
(* Debugging                                                                 *)
(*****************************************************************************)

let checking = true

let print_to_stdout file =
  (* Printer takes into account annotations *)
  let printer = new Printer.print () in
  Log.print_on_output (Extlib.swap (Cil.printFile printer) file)

class checkTypes =
  let preaction_expr e = ignore (typeOf e); e in
object

  inherit Visitor.generic_frama_c_visitor
    (Project.current ()) (Cil.inplace_visit ()) as super

  method vexpr e =
    ChangeDoChildrenPost (preaction_expr e, fun x -> x)

(* I comment on purpose additional verifications, because they cause some tests
   to fail, see e.g. [copy_struct], because term-lhost TResult does not have
   a type for a proper conversion to expression. *)

(*   method vterm = *)
(*     do_on_term (Some preaction_expr,None) *)

end

let check_types file =
  (* check types *)
  let visitor = new checkTypes in
  visitFramacFile visitor file;
  (* check general consistency *)
(*   Cil.visitCilFile (new File.check_file :> Cil.cilVisitor) file *)

class check_file: Visitor.frama_c_visitor  =
object(self)

  inherit Visitor.generic_frama_c_visitor
    (Project.current ()) (Cil.inplace_visit ()) as super

  val known_fields = Cil_datatype.Fieldinfo.Hashtbl.create 7

  method vterm t =
    match t.term_node with
      | TLval _ ->
	  begin match t.term_type with
	    | Ctype ty when isVoidType ty ->
		Jessie_options.fatal ~current:true "Term %a has void type" !Ast_printer.d_term t
	    | _ -> DoChildren
	  end
      | _ -> DoChildren

  method voffs = function
      NoOffset -> SkipChildren
    | Index _ -> DoChildren
    | Field(fi,_) ->
        begin
          try
            if not (fi == Cil_datatype.Fieldinfo.Hashtbl.find known_fields fi)
            then
	      Jessie_options.warning ~current:true
		"Field %s of type %s is not shared between declaration and use"
                fi.fname fi.fcomp.cname
          with Not_found ->
	    Jessie_options.warning ~current:true
	      "Field %s of type %s is unbound in the AST"
              fi.fname fi.fcomp.cname
        end;
        DoChildren

  method vterm_offset = function
      TNoOffset -> SkipChildren
    | TIndex _ -> DoChildren
    | TField(fi,_) ->
        begin
          try
            if not (fi == Cil_datatype.Fieldinfo.Hashtbl.find known_fields fi)
            then
              Jessie_options.warning ~current:true
		"Field %s of type %s is not shared between declaration and use"
                fi.fname fi.fcomp.cname
	  with Not_found ->
	    Jessie_options.warning ~current:true
	      "Field %s of type %s is unbound in the AST"
               fi.fname fi.fcomp.cname
        end;
        DoChildren

  method vinitoffs = self#voffs

  method vglob_aux = function
      GCompTag(c,_) ->
        List.iter
          (fun x -> Cil_datatype.Fieldinfo.Hashtbl.add known_fields x x) c.cfields;
        DoChildren
    | _ -> DoChildren

end


(*****************************************************************************)
(* Miscellaneous                                                             *)
(*****************************************************************************)

(* Queries *)

let is_base_addr t = match (stripTermCasts t).term_node with
  | Tbase_addr _ -> true
  | _ -> false

(* Smart constructors *)

(* Redefine statement constructor of CIL to create them with valid sid *)
let mkStmt = mkStmt ~valid_sid:true

let mkterm tnode ty loc =
  {
    term_node = tnode;
    term_loc = loc;
    term_type = ty;
    term_name = []
  }

let term_of_var v =
  let lv = cvar_to_lvar v in
  if app_term_type isArrayType false lv.lv_type then
    let ptrty =
      TPtr(force_app_term_type element_type lv.lv_type,[])
    in
    mkterm (TStartOf(TVar lv,TNoOffset)) (Ctype ptrty) v.vdecl
  else
    mkterm (TLval(TVar lv,TNoOffset)) lv.lv_type v.vdecl

let mkpred pnode loc =
  {
    ip_name = [];
    ip_loc = loc;
    ip_id = Logic_const.fresh_predicate_id ();
    ip_content = pnode;
  }

let mkInfo e =
  match e.enode with
      Info _ -> e
    | _ ->
        let einfo = { exp_type = Ctype voidType; exp_name = [] } in
        (* In many cases, the correct type may not be available, as
         * the expression may result from a conversion from a term or a tset.
         * Calling [typeOf] on such an expression may raise an error.
         * Therefore, put here a dummy type until tsets correctly typed.
         *)
        new_exp ~loc:e.eloc (Info(e,einfo))

(* Manipulation of offsets *)

let rec offset_list = function
  | NoOffset -> []
  | Field (fi,off) -> (Field (fi, NoOffset)) :: offset_list off
  | Index (e,off) -> (Index (e, NoOffset)) :: offset_list off

let is_last_offset = function
  | NoOffset -> true
  | Field (_fi,NoOffset) -> true
  | Field (_fi,_) -> false
  | Index (_e,NoOffset) -> true
  | Index (_e,_) -> false

(* Transform an index on a multi-dimensional array into an index on the
 * same array that would be flattened to a single dimensional array.
 *)
let rec lift_offset ty = function
  | Index(idx1,(Index(idx2, _off) as suboff)) ->
      let subty = direct_element_type ty in
      let siz = array_size subty in
      begin match lift_offset subty suboff with
	| Index(idx, off) ->
	    let mulidx =
              new_exp ~loc:idx2.eloc
                (BinOp(Mult,idx1,constant_expr siz,intType)) in
	    (* Keep info at top-level for visitors on terms that where
	     * translated to expressions. Those expect these info when
	     * translating back to term.
	     *)
	    let addidx =
	      map_under_info
                (fun e ->
                   new_exp ~loc:e.eloc (BinOp(PlusA,mulidx,idx,intType))) idx1
	    in
	    Index(addidx,off)
	| _ -> assert false
      end
  | Index(idx1,NoOffset) as off ->
      let subty = direct_element_type ty in
      if isArrayType subty then
	let siz = array_size subty in
	(* Keep info at top-level *)
	let mulidx =
	  map_under_info
	    (fun e ->
               new_exp ~loc:e.eloc
                 (BinOp(Mult,idx1,constant_expr siz,intType)))
            idx1
	in
	Index(mulidx,NoOffset)
      else off
  | off -> off

let change_idx idx1 idx siz =
  let boff =
    Logic_utils.mk_dummy_term (TBinOp(Mult,idx1,constant_term Cil_datatype.Location.unknown siz))
      intType
  in
  Logic_utils.mk_dummy_term (TBinOp(PlusA,boff,idx)) intType

let rec lift_toffset ty off =
  match off with
      TIndex(idx1,(TIndex _ as suboff)) ->
        let subty = direct_element_type ty in
        let siz = array_size subty in
        begin match lift_toffset subty suboff with
            | TIndex(idx,off) -> TIndex(change_idx idx1 idx siz,off)
            | TField _ | TNoOffset -> assert false
        end
    | TIndex(idx1,TNoOffset) ->
        let subty = direct_element_type ty in
        if isArrayType subty then
          let siz = array_size subty in
          TIndex(change_idx
                   idx1 
                   (constant_term Cil_datatype.Location.unknown My_bigint.zero) 
                   siz,
                 TNoOffset)
        else off
    | TIndex _ | TField _ | TNoOffset -> off

(* Allocation/deallocation *)

let malloc_function () =
  try
    Kernel_function.get_vi (Globals.Functions.find_by_name "malloc")
  with Not_found ->
    let params = Some ["size",uintType,[]] in
    let f =
      findOrCreateFunc
	(Ast.get ()) "malloc" (TFun(voidPtrType,params,false,[]))
    in
    let prm =
      try
        List.hd (Cil.getFormalsDecl f)
      with Not_found | Invalid_argument _ ->
        fatal "unexpected prototype for malloc"
    in
    let range = 
      Logic_const.trange 
        (Some (Cil.lzero ()), 
         Some (Logic_const.tvar (Cil.cvar_to_lvar prm)))
    in
    let typ = Ctype Cil.charPtrType in
    let base =
      Logic_const.term 
        (TCastE(Cil.charPtrType,Logic_const.tresult Cil.charPtrType)) typ
    in
    let alloc = 
      Logic_const.new_identified_term
        (Logic_const.term (TBinOp(PlusPI,base,range)) typ)
    in
    let behav = {
      b_name = Cil.default_behavior_name;
      b_assumes = [];
      b_requires = [];
      b_extended = [];
      b_assigns = Writes [];
      b_allocation = FreeAlloc([alloc],[]);
      b_post_cond = [];
    } in
    let spec = { (empty_funspec ()) with spec_behavior = [behav]; } in
    Globals.Functions.replace_by_declaration spec f Cil_datatype.Location.unknown;
    f

let free_function () =
  try
    Kernel_function.get_vi (Globals.Functions.find_by_name "free")
  with Not_found ->
    let params = Some ["ptr",voidPtrType,[]] in
    let f =
      findOrCreateFunc
	(Ast.get ()) "free" (TFun(voidType,params,false,[]))
    in
    let prm =
      try
        List.hd (Cil.getFormalsDecl f)
      with Not_found | Invalid_argument _ ->
        fatal "unexpected prototype for free"
    in
    let frees = 
      Logic_const.new_identified_term
        (Logic_const.tvar (Cil.cvar_to_lvar prm))
    in
    let behav = {
      b_name = Cil.default_behavior_name;
      b_assumes = [];
      b_post_cond = [];
      b_requires = [];
      b_extended = [];
      b_allocation = FreeAlloc([],[frees]);
      b_assigns = Writes [];
    } 
    in
    let spec = { (empty_funspec ()) with spec_behavior = [behav]; } in
    Globals.Functions.replace_by_declaration spec f Cil_datatype.Location.unknown;
    f

let mkalloc v ty loc =
  let callee = new_exp ~loc (Lval(Var(malloc_function ()),NoOffset)) in
  let arg = sizeOf ~loc ty in
  Call(Some(Var v,NoOffset),callee,[arg],loc)

let mkalloc_statement v ty loc = mkStmt (Instr(mkalloc v ty loc))

let mkalloc_array v ty num loc =
  let callee = new_exp ~loc (Lval(Var(malloc_function ()),NoOffset)) in
  let arg = constant_expr 
    (My_bigint.of_int64 (Int64.mul num (Int64.of_int (sizeOf_int ty))))
  in
  Call(Some(Var v,NoOffset),callee,[arg],loc)

let mkalloc_array_statement v ty num loc =
  mkStmt (Instr(mkalloc_array v ty num loc))

let mkfree v loc =
  let callee = new_exp ~loc (Lval(Var(free_function ()),NoOffset)) in
  let arg = new_exp ~loc (Lval(Var v,NoOffset)) in
  Call(None,callee,[arg],loc)

let mkfree_statement v loc = mkStmt (Instr(mkfree v loc))

(*
Local Variables:
compile-command: "LC_ALL=C make -C .. -j byte"
End:
*)
