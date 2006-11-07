

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast


let add_field_writes ef fi =
  { (* ef with *) jc_writes_fields = FieldSet.add fi ef.jc_writes_fields }
 
let ef_union ef1 ef2 =
  { 
    jc_writes_fields = FieldSet.union 
			 ef1.jc_writes_fields ef2.jc_writes_fields ;
  }
let same_effects ef1 ef2 =
  FieldSet.equal ef1.jc_writes_fields ef2.jc_writes_fields


(* $Id: jc_effect.ml,v 1.4 2006-11-07 13:25:28 marche Exp $ *)

let rec expr ef e =
  match e.jc_expr_node with
    | JCEconst _ -> ef
    | JCEassign_heap (e1, fi, e2) 
    | JCEassign_op_heap(e1,fi,_,e2) ->
	expr (expr (add_field_writes ef fi) e1) e2
    | JCEassign_op_local (_, _, _) -> assert false
    | JCEassign_local (_, _) -> assert false
    | JCEcall (fi, le) -> 
	ef_union fi.jc_fun_info_effects
	  (List.fold_left expr ef le)
    | JCEderef (e, f) -> expr ef e (* TODO *)
    | JCEshift (_, _) -> assert false
    | JCEvar _ -> ef (* TODO *)

let rec statement ef s =
  match s.jc_statement_node with
    | JCSexpr e -> expr ef e
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false
    | JCSgoto _ -> assert false
    | JCScontinue _ -> assert false
    | JCSbreak _ -> assert false
    | JCSreturn e -> expr ef e
    | JCSwhile (_, _, _) -> assert false
    | JCSif (e, s1, s2) -> 
	statement (statement (expr ef e) s1) s2
    | JCSdecl _ -> assert false
    | JCSassert _ -> assert false
    | JCSblock _ -> assert false
    | JCSskip -> assert false


let location ef l =
  match l with
    | JCLderef(t,fi) ->
	add_field_writes ef fi
    | JCLvar _ -> assert false (* TODO *)

let behavior ef (_,b) =
  Option_misc.fold 
    (fun x ef -> List.fold_left location ef x) 
    b.jc_behavior_assigns ef

let spec ef s = 
  List.fold_left behavior ef s.jc_fun_behavior

(* computing the fixpoint *)

let fixpoint_reached = ref false

let fun_effects fi =
  let (f,s,b) = 
    Hashtbl.find Jc_typing.functions_table fi.jc_fun_info_tag 
  in
  let ef = f.jc_fun_info_effects in
  let ef = spec ef s in
  let ef = List.fold_left statement ef b in
  if same_effects ef f.jc_fun_info_effects then ()
  else begin
    fixpoint_reached := false;
    f.jc_fun_info_effects <- ef
  end
    
  
open Format
open Pp

let function_effects funs =
  fixpoint_reached := false;
  while not !fixpoint_reached do
    fixpoint_reached := true;
    Jc_options.lprintf "Effects: doing one iteration...@.";
    List.iter fun_effects funs
  done;
  Jc_options.lprintf "Effects: fixpoint reached@.";
  List.iter
    (fun f ->
       Jc_options.lprintf
	 "Effects for function %s:\n%a@." f.jc_fun_info_name
	 (print_list comma (fun fmt field ->
			     fprintf fmt "%s" field.jc_field_info_name))
	 (FieldSet.elements f.jc_fun_info_effects.jc_writes_fields))
    funs

       

  
