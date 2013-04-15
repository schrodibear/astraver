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



(* TODO:

   - In both retyping phases that add a level of indirection to locals:
       - Retype variables of structure type
       - Retype variables and fields whose address is taken
     If the returned value dereferences a local, take the returned value in
     a temporary before deallocating memory for the local variable and
     returning. Mostly an issue of consistency: since it is a local variable
     involved, it is retyped as a reference and no check is issued for
     validity of dereference.
     See ex roux3.c from Jessie test base.
     Thanks to Pierre Roux for noting this.

*)


(* Import from Cil *)
open Cil_types
open Cil
open Ast_info
open Extlib

open Visitor

(* Utility functions *)
open Common

let label_here = LogicLabel(None,"Here")

(*****************************************************************************)
(* Retype variables of array type.                                           *)
(*****************************************************************************)

(* TODO: retype predicate \valid_index and \valid_range
 * E.g. in example array.c, "\valid_index(t,1)" for "t" being typed as
 * "int t[3][3]", should be transformed into "\valid_range(t,3,5)".
 *)
class retypeArrayVariables =

  (* Variables originally of array type *)
  let varset = ref Cil_datatype.Varinfo.Set.empty in
  let lvarset = ref Cil_datatype.Logic_var.Set.empty in

  (* Correspondance between variables and "straw" variables, that are used to
   * replace the variable after some changes have been made on the AST,
   * so that further exploration does not change it anymore. The "straw"
   * variables are replaced by regular one before returning the modified AST.
   *)
  let var_to_strawvar = Cil_datatype.Varinfo.Hashtbl.create 17 in
  let strawvar_to_var = Cil_datatype.Varinfo.Hashtbl.create 17 in
  let lvar_to_strawlvar = Cil_datatype.Logic_var.Hashtbl.create 17 in
  let strawlvar_to_lvar = Cil_datatype.Logic_var.Hashtbl.create 17 in

  (* Variables to allocate *)
  let allocvarset = ref Cil_datatype.Varinfo.Set.empty in
  let alloclvarset = ref Cil_datatype.Logic_var.Set.empty in

  (* Remember original array type even after variable modified *)
  let var_to_array_type : typ Cil_datatype.Varinfo.Hashtbl.t = Cil_datatype.Varinfo.Hashtbl.create 0 in
  let lvar_to_array_type = Cil_datatype.Logic_var.Hashtbl.create 17 in

  (* As the rule would be reentrant, do not rely on the fact it is idempotent,
   * and rather change the variable into its "straw" counterpart, as it is
   * done in [preaction_expr]. Also make sure every top expression inside
   * a left-value is an [Info], so that terms that were converted to
   * expressions before treatment can be safely converted back.
   *)
  let preaction_lval (host,off as lv) =
    match host with
      | Var v ->
          if Cil_datatype.Varinfo.Set.mem v !varset then begin
            let strawv = Cil_datatype.Varinfo.Hashtbl.find var_to_strawvar v in
            let loc = Cil_const.CurrentLoc.get() in
            let host = Mem(mkInfo(new_exp ~loc (Lval(Var strawv,NoOffset)))) in
            let off =
              lift_offset (Cil_datatype.Varinfo.Hashtbl.find var_to_array_type v) off
            in
            host, off
          end else
            lv (* For terms, also corresponds to the case for Result *)
      | Mem _ -> lv
  in

  let postaction_lval (host,off as lv) =
    match host with
      | Var strawv ->
          begin try
            let v = Cil_datatype.Varinfo.Hashtbl.find strawvar_to_var strawv in
            Var v, off
          with Not_found -> lv end
      | Mem _ -> lv
  in

  let rec preaction_expr e =
    let loc = e.eloc in
    match e.enode with
    | StartOf(Var v,off) ->
        if Cil_datatype.Varinfo.Set.mem v !varset then begin
          let ty = Cil_datatype.Varinfo.Hashtbl.find var_to_array_type v in
          let strawv = Cil_datatype.Varinfo.Hashtbl.find var_to_strawvar v in
          match lift_offset ty off with
            | NoOffset -> new_exp ~loc (Lval(Var strawv,NoOffset))
            | Index(ie,NoOffset) ->
                let ptrty = TPtr(element_type ty,[]) in
                new_exp ~loc (BinOp(PlusPI,
                               new_exp ~loc (Lval(Var strawv,NoOffset)),
                               ie,ptrty))
            | Index _ | Field _ ->
                (* Field with address taken treated separately *)
                new_exp ~loc
                  (StartOf
                     (Mem(new_exp ~loc (Lval(Var strawv,NoOffset))),off))
        end else e
    | AddrOf(Var v,off) ->
        if Cil_datatype.Varinfo.Set.mem v !varset then 
          begin
            let ty = Cil_datatype.Varinfo.Hashtbl.find var_to_array_type v in
            let strawv = Cil_datatype.Varinfo.Hashtbl.find var_to_strawvar v in
            match lift_offset ty off with
              | Index(ie,NoOffset) ->
                  let ptrty = TPtr(element_type ty,[]) in
                  new_exp ~loc
                    (BinOp(PlusPI,
                           new_exp ~loc (Lval(Var strawv,NoOffset)), ie,ptrty))
              | NoOffset -> 
                  unsupported "this instance of the address operator cannot be handled"
              | Index _ | Field _ ->
                  (* Field with address taken treated separately *)
                  new_exp ~loc
                    (AddrOf(Mem(new_exp ~loc (Lval(Var strawv,NoOffset))),off))
          end 
        else e
    | BinOp(PlusPI,e1,e2,opty) ->
        begin match (stripInfo e1).enode with
          | StartOf(Var v,off) ->
              let rec findtype ty = function
                | NoOffset -> ty
                | Index(_, roff) ->
                    findtype (direct_element_type ty) roff
                | Field _ -> raise Not_found
              in
              if Cil_datatype.Varinfo.Set.mem v !varset then
                let ty = Cil_datatype.Varinfo.Hashtbl.find var_to_array_type v in
                (* Do not replace [v] by [strawv] here, as the sub-expression
                 * [e1] should be treated first. Do it right away so that
                 * the resulting AST is well-typed, which is crucial to apply
                 * this on expressions obtained from terms.
                 *)
                let e1 = preaction_expr e1 in
                let ty = findtype ty off in
                let subty = direct_element_type ty in
                if isArrayType subty then
                  let siz = array_size subty in
                  let e2 =
                    new_exp ~loc:e2.eloc
                      (BinOp(Mult,e2,constant_expr siz,intType)) in
                  new_exp ~loc (BinOp(PlusPI,e1,e2,opty))
                else e
              else e
          | _ -> e
        end
    | _ -> e
  in
object(self)

  inherit Visitor.frama_c_inplace

  method vvdec v =
    if isArrayType v.vtype && not (Cil_datatype.Varinfo.Set.mem v !varset) then
      begin
        assert (not v.vformal);
        Cil_datatype.Varinfo.Hashtbl.add var_to_array_type v v.vtype;
        let elemty = element_type v.vtype in
        (* Store information that variable was originally of array type *)
        varset := Cil_datatype.Varinfo.Set.add v !varset;
        (* Change the variable type *)
        let newty =
          if Integer.gt (array_size v.vtype) Integer.zero then
            begin
              (* Change the type into "reference" type, that behaves almost like
               * a pointer, except validity is ensured.
               *)
              let size = constant_expr (array_size v.vtype) in
              (* Schedule for allocation *)
              allocvarset := Cil_datatype.Varinfo.Set.add v !allocvarset;
              mkTRefArray(elemty,size,[]);
            end
          else
            (* Plain pointer type to array with zero size *)
            TPtr(v.vtype,[]);
        in
        attach_globaction (fun () -> v.vtype <- newty);
        (* Create a "straw" variable for this variable, with the correct type *)
         let strawv = makePseudoVar newty in
        Cil_datatype.Varinfo.Hashtbl.add var_to_strawvar v strawv;
        Cil_datatype.Varinfo.Hashtbl.add strawvar_to_var strawv v;
      end;
    DoChildren

  method vlogic_var_decl lv =
    if not (Cil_datatype.Logic_var.Hashtbl.mem lvar_to_strawlvar lv) &&
      app_term_type isArrayType false lv.lv_type then
      begin
        Cil_datatype.Logic_var.Hashtbl.add lvar_to_array_type lv
          (force_app_term_type (fun x -> x) lv.lv_type);
        let elemty = force_app_term_type element_type lv.lv_type in
        lvarset := Cil_datatype.Logic_var.Set.add lv !lvarset;
        let newty =
          if Integer.gt 
            (force_app_term_type array_size lv.lv_type) 
            Integer.zero 
          then
            begin
              let size =
                constant_expr (force_app_term_type array_size lv.lv_type)
              in alloclvarset := Cil_datatype.Logic_var.Set.add lv !alloclvarset;
              mkTRefArray(elemty,size,[])
            end
          else TPtr(elemty,[])
        in attach_globaction (fun () -> lv.lv_type <- Ctype newty);
        let strawlv = match lv.lv_origin with
            None -> make_temp_logic_var (Ctype newty)
          | Some v -> cvar_to_lvar (Cil_datatype.Varinfo.Hashtbl.find var_to_strawvar v)
        in
        Cil_datatype.Logic_var.Hashtbl.add lvar_to_strawlvar lv strawlv;
        Cil_datatype.Logic_var.Hashtbl.add strawlvar_to_lvar strawlv lv
      end;
      DoChildren

  method vglob_aux g = match g with
    | GVar(v,_init,_loc) ->
        (* Make sure variable declaration is treated before definition *)
        ignore (Cil.visitCilVarDecl (self:>Cil.cilVisitor) v);
        if Cil_datatype.Varinfo.Set.mem v !allocvarset then
          (* Allocate memory for new reference variable *)
          let ty = Cil_datatype.Varinfo.Hashtbl.find var_to_array_type v in
          let size = array_size ty in
(* Disabled: anyway, it is useless to generate code for that,
   a post-condition should be generated instead (bts0284)
          let elemty = element_type ty in
          let ast = mkalloc_array_statement v elemty (array_size ty) loc in
          attach_globinit ast;
*)
          (* Define a global validity invariant *)
          let p =
            Logic_const.pvalid_range
              ~loc:v.vdecl
              (label_here,
               variable_term v.vdecl (cvar_to_lvar v),
               constant_term v.vdecl Integer.zero,
               constant_term v.vdecl (Integer.pred size))
          in
          let globinv =
	    Cil_const.make_logic_info (unique_logic_name ("valid_" ^ v.vname)) in
          globinv.l_labels <- [ label_here ];
          globinv.l_body <- LBpred p;
          attach_globaction (fun () -> Logic_utils.add_logic_function globinv);
          ChangeTo [g;GAnnot(Dinvariant (globinv,v.vdecl),v.vdecl)]
        else DoChildren
    | GVarDecl _ | GFun _ | GAnnot _ -> DoChildren
    | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method vfunc f =
    (* First change type of local array variables *)
    List.iter (ignore $ Cil.visitCilVarDecl (self:>Cil.cilVisitor)) f.slocals;
    List.iter (ignore $ Cil.visitCilVarDecl (self:>Cil.cilVisitor)) f.sformals;
    (* Then allocate/deallocate memory for those that need it *)
    List.iter (fun v ->
      if Cil_datatype.Varinfo.Set.mem v !allocvarset then
        let ty = Cil_datatype.Varinfo.Hashtbl.find var_to_array_type v in
        let elemty = element_type ty in
        let ast = mkalloc_array_statement v elemty 
          (Integer.to_int64 (array_size ty)) v.vdecl 
        in
        add_pending_statement ~beginning:true ast;
        let fst = mkfree_statement v v.vdecl in
        add_pending_statement ~beginning:false fst
    ) f.slocals;
    DoChildren

  method vlval lv =
    ChangeDoChildrenPost (preaction_lval lv, postaction_lval)

  method vterm_lval lv =
    do_on_term_lval (Some preaction_lval, Some postaction_lval) lv

  method vexpr e =
    ChangeDoChildrenPost (preaction_expr e, fun x -> x)

  method vterm =
    do_on_term (Some preaction_expr, None)

end

let retype_array_variables file =
  (* Enforce the prototype of malloc to exist before visiting anything.
     It might be useful for allocation pointers from arrays
  *)
  ignore (Common.malloc_function ());
  ignore (Common.free_function ());
  let visitor = new retypeArrayVariables in
  visit_and_push_statements visit_and_update_globals visitor file


(*****************************************************************************)
(* Retype logic functions/predicates with structure parameters or return.    *)
(*****************************************************************************)

let model_fields_table = Hashtbl.create 7

let model_fields compinfo =
  (* Format.eprintf "looking in model_fields_table for %s@." compinfo.cname; *)
  try
    Hashtbl.find model_fields_table compinfo.ckey
  with Not_found -> []


(* logic parameter:
 * - change parameter type to pointer to structure
 * - change uses of parameters in logical annotations
 * TODO: take care of logic variables introduced by let.
 *)
class retypeLogicFunctions =

  let varset = ref Cil_datatype.Logic_var.Set.empty in
  let this_name : string ref = ref "" in
  let change_this_type = ref false in  (* Should "this" change? *)
  let new_result_type = ref (Ctype voidType) in
  let change_result_type = ref false in (* Should Result change? *)

  let var lv =
    match lv.lv_type with
      | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> ()
      | Ctype ty ->
          if isStructOrUnionType ty then
            unsupported "Jessie plugin does not support struct or union as parameter to logic functions. Please use a pointer instead."
                      (*
          if isStructOrUnionType ty then
            begin
              varset := Cil_datatype.Logic_var.Set.add lv !varset;
              lv.lv_type <- Ctype(mkTRef ty);
              match lv.lv_origin with
                | None -> ()
                | Some v ->
                    (* For some obscure reason, logic function/predicate
                     * parameters are C variables.
                     *)
                    v.vtype <- mkTRef ty
            end
                      *)
  in

  let postaction_term_lval (host,off) =
    let host = match host with
      | TVar lv ->
          (* Oddly, "this" variable in type invariant is not declared
             before use. Change its type on the fly.
          *)
          if !change_this_type && lv.lv_name = !this_name then
            var lv;
          if Cil_datatype.Logic_var.Set.mem lv !varset then
            let tlval =
              mkterm (TLval(host,TNoOffset)) lv.lv_type
                (Cil_const.CurrentLoc.get())
            in
            TMem tlval
          else host
      | TResult _ ->
          if !change_result_type then
            match !new_result_type with
                Ctype typ ->
                  let tlval = Logic_const.tresult typ in TMem tlval
              | _ -> assert false (* result type of C function
                                     must be a C type*)
          else host
      | TMem _t -> host
    in
    host, off
  in
object

  inherit Visitor.frama_c_inplace

  method vannotation =
    let return_type ty =
      change_result_type := false;
      match ty with
        | Ctype rt when isStructOrUnionType rt ->
            begin
              change_result_type := true;
              let ty = Ctype(mkTRef rt "Norm.vannotation") in
              new_result_type := ty;
              ty
            end
        | Ctype _ | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> ty
    in
    let annot = function
      | Dfun_or_pred (li,loc) ->
          List.iter var li.l_profile;
          begin
            match li.l_type with
              | None -> DoChildren
              | Some rt ->
                  let li' = { li with l_type = Some (return_type rt)}  in
                  ChangeDoChildrenPost (Dfun_or_pred (li',loc), fun x -> x)
          end
      | Dtype_annot (annot,loc) ->
          begin match (List.hd annot.l_profile).lv_type with
            | Ctype ty when isStructOrUnionType ty ->
                change_this_type := true;
                this_name := (List.hd annot.l_profile).lv_name;
                let annot = { annot with
                                l_profile = [{ (List.hd annot.l_profile) with
                                                 lv_type = Ctype(mkTRef ty "Norm.annot, Dtype_annot")}];
                }
                in
                ChangeDoChildrenPost
                  (Dtype_annot (annot,loc), fun x -> change_this_type := false; x)
            | Ctype _ | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ ->
                DoChildren
          end
      | Dtype _ | Dlemma _ | Dinvariant _ | Dvolatile _  -> DoChildren
      | Daxiomatic _ -> DoChildren (* FIXME: correct ? *)
      | Dmodel_annot (mi,_) -> 
          begin
            match unrollType mi.mi_base_type with
              | TComp (ci, _, _) ->
                  begin
                    let l = 
                      try Hashtbl.find model_fields_table ci.ckey
                      with Not_found -> []
                    in
                    (* Format.eprintf "filling model_fields_table for %s@." ci.cname; *)
                    Hashtbl.replace model_fields_table ci.ckey (mi::l)
                  end
              | _ -> 
              Common.unsupported "model field only on structures"
          end;
          DoChildren (* FIXME: correct ? *)
      | Dcustom_annot _ -> DoChildren (* FIXME: correct ? *)
    in annot

  method vterm_lval tlv =
    ChangeDoChildrenPost (tlv, postaction_term_lval)

  method vterm t =
    let preaction_term t =
      match t.term_node with
        | Tapp(callee,labels,args) ->
            let args = List.map (fun arg ->
              (* Type of [arg] has not been changed. *)
              match arg.term_type with
                | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> arg
                | Ctype ty ->
                    if isStructOrUnionType ty then
                      match arg.term_node with
                        | TLval lv ->
                            (* Arguments translated under address here may
                             * be translated back to dereference when treating
                             * left-values. This is why we add a normalization
                             * in [postaction_term]. *)
                            {
                              arg with
                                term_node = TAddrOf lv;
                                term_type = Ctype(mkTRef ty "Norm.vterm");
                            }
                        | _ -> assert false (* Should not be possible *)
                    else arg
            ) args in
            { t with term_node = Tapp(callee,labels,args); }
        | _ -> t
    in
    (* Renormalize the term tree. *)
    let postaction_term t =
      match t.term_node with
        | TAddrOf(TMem t,TNoOffset) -> t
        | _ -> t
    in
    ChangeDoChildrenPost (preaction_term t, postaction_term)

  method vpredicate = function
    | Papp(callee,labels,args) ->
        let args = List.map (fun arg ->
          (* Type of [arg] has not been changed. *)
          match arg.term_type with
            | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> arg
            | Ctype ty ->
                if isStructOrUnionType ty then
                  match arg.term_node with
                    | TLval lv ->
                        {
                          arg with
                            term_node = TAddrOf lv;
                            term_type = Ctype(mkTRef ty "Norm.vpredicate");
                        }
                    | _ -> assert false (* Should not be possible *)
                else arg
        ) args in
        ChangeDoChildrenPost (Papp(callee,labels,args), fun x -> x)
    | _ -> DoChildren

end

let retype_logic_functions file =
  let visitor = new retypeLogicFunctions in
  visitFramacFile visitor file


(*****************************************************************************)
(* Expand structure copying through parameter, return or assignment.         *)
(*****************************************************************************)

let return_vars = Cil_datatype.Varinfo.Hashtbl.create 17

(* parameter:
 * - if function defined, add local copy variable of structure type
 * - change parameter type to pointer to structure
 * - change type at call-site to take address of structure arguments
 * - change uses of parameters in logical annotations
 * return:
 * - change return type to pointer to structure
 * - add temporary variable for call
 * - free allocated memory for return after call
 * assignment:
 * - recursively decompose into elementary assignments
 *)
class expandStructAssign () =

  let pairs = ref [] in
  let new_return_type = ref None in
  let return_var = ref None in

  let postaction_term_lval (host,off) =
    let host = match host with
      | TResult _ ->
          begin match !new_return_type with
              None -> host
            | Some rt ->
            let tlval = Logic_const.tresult rt in TMem tlval
          end
      | TVar v ->
          begin match v.lv_origin with
          | None -> host
              (* TODO: recognize \result variable, and change its use if
                 of reference type here. *)
          | Some cv ->
              try
                let newv = List.assoc cv !pairs in
                let newlv = cvar_to_lvar newv in
                (* Type of [newv] is set at that point. *)
                let tlval =
                  mkterm (TLval(TVar newlv,TNoOffset)) (Ctype newv.vtype)
                    (Cil_const.CurrentLoc.get())
                in
                TMem tlval
              with Not_found -> TVar v
          end
      | TMem _t -> host
    in
    host, off
  in

  let rec expand_assign lv e ty loc =
    match unrollType ty with
      | TComp(mcomp,_,_) ->
          let field fi =
            let newlv = addOffsetLval (Field(fi,NoOffset)) lv in
            let newe = match e.enode with
              | Lval elv ->
                  new_exp ~loc:e.eloc
                    (Lval(addOffsetLval (Field(fi,NoOffset)) elv))
              | _ ->
                  (* Other possibilities like [CastE] should have been
                     transformed at this point. *)
                  assert false
            in
            expand_assign newlv newe fi.ftype loc
          in
          List.flatten (List.map field mcomp.cfields)
      | TArray _ ->
          let elem i =
            let cste = constant_expr i in
            let newlv = addOffsetLval (Index(cste,NoOffset)) lv in
            let newe = match e.enode with
              | Lval elv ->
                  new_exp ~loc:e.eloc
                    (Lval (addOffsetLval (Index(cste,NoOffset)) elv))
              | _ ->
                  (* Other possibilities like [CastE] should have been
                     transformed at this point. *)
                  assert false
            in
            expand_assign newlv newe (direct_element_type ty) loc
          in
          let rec all_elem acc i =
            if Integer.ge i Integer.zero
            then all_elem (elem i @ acc) (Integer.pred i) 
            else acc
          in
          assert (not (is_reference_type ty));
          all_elem [] (Integer.pred (direct_array_size ty))
      | _ -> [Set (lv, e, loc)]
  in

  let rec expand lv ty loc =
    match unrollType ty with
      | TComp(mcomp,_,_) ->
          let field fi =
            let newlv = addOffsetLval (Field(fi,NoOffset)) lv in
            expand newlv fi.ftype loc
          in
          List.flatten (List.map field mcomp.cfields)
      | TArray _ ->
          let elem i =
            let cste = constant_expr i in
            let newlv = addOffsetLval (Index(cste,NoOffset)) lv in
            expand newlv (direct_element_type ty) loc
          in
          let rec all_elem acc i =
            if Integer.ge i Integer.zero then
              all_elem (elem i @ acc) (Integer.pred i)
            else acc
          in
          assert (not (is_reference_type ty));
          all_elem [] (Integer.pred (direct_array_size ty))
      | _ -> [ lv ]
  in

object(self)

  inherit Visitor.frama_c_inplace
  method vglob_aux =
    let retype_func fvi =
      let formal (n,ty,a) =
        let ty = 
          if isStructOrUnionType ty then mkTRef ty "Norm.vglob_aux" else ty
        in
        n, ty, a
      in
      let rt,params,isva,a = splitFunctionTypeVI fvi in
      let params = match params with
        | None -> None
        | Some p -> Some(List.map formal p)
      in
      let rt = 
        if isStructOrUnionType rt then
          mkTRef rt "Norm.vglob_aux(2)" 
        else rt 
      in
      fvi.vtype <- TFun(rt,params,isva,a)
    in
    function
      | GVarDecl(_spec,v,_attr) ->
          if isFunctionType v.vtype && not v.vdefined then retype_func v;
          DoChildren
      | GFun _
      | GAnnot _ -> DoChildren
      | GVar _  | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
      | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method vfunc f =
    let var v =
      if isStructOrUnionType v.vtype then
        let newv = copyVarinfo v (unique_name ("v_" ^ v.vname)) in
        newv.vtype <- mkTRef newv.vtype "Norm.vfunc";
        v.vformal <- false;
        let rhs =
          new_exp ~loc:v.vdecl
            (Lval
               (mkMem
                  (new_exp ~loc:v.vdecl (Lval(Var newv,NoOffset))) NoOffset))
        in
        let copy = mkassign_statement (Var v,NoOffset) rhs v.vdecl in
        add_pending_statement ~beginning:true copy;
        pairs := (v,newv) :: !pairs;
        [v], newv
      else
        [], v
    in
    (* Insert copy statements. *)
    let locvl,formvl = List.split (List.map var f.sformals) in
    (* Set locals and formals. *)
    let locvl = List.flatten locvl in
    f.slocals <- locvl @ f.slocals;
    setFormals f formvl;
    (* Add local variable for return *)
    let rt = getReturnType f.svar.vtype in
    if isStructOrUnionType rt then
      let rv = makeTempVar (Extlib.the self#current_func) rt in
      return_var := Some rv;
      Cil_datatype.Varinfo.Hashtbl.add return_vars rv ()
    else
      return_var := None;
    (* Change return type. *)
    new_return_type :=
      if isStructOrUnionType rt then Some(mkTRef rt "Norm.vfunc(3)") else None;
    let rt = if isStructOrUnionType rt then mkTRef rt "Norm.vfunc(4)" else rt in
    setReturnType f rt;
    DoChildren

  method vbehavior b =
    let lval loc lv = expand lv (typeOfLval lv) loc in
    let term t = match t.term_node with
      | TLval tlv ->
          let lv,env = Common.force_term_lval_to_lval tlv in
          let lvlist = lval t.term_loc lv in
          let tslvlist =
            List.map (Common.force_back_lval_to_term_lval env)
              lvlist
          in
          List.map (fun
                      tslv ->
                        Logic_const.term ~loc:t.term_loc (TLval tslv)
                          t.term_type
                   ) tslvlist
      | Tempty_set -> [ t ]
          (* most of the case below are still to do*)
      | TStartOf _
      | TConst _
      | TCastE _
      | TLogic_coerce _
      | Tat _
      | TAddrOf _
      | Tapp _
      | Trange _
      | Tunion _
      | Tinter _
      | Tcomprehension _
      | Tif _
      | Tnull -> [ t ]
        (* those cases can not appear as assigns *)
      | TSizeOf _ | TSizeOfE _ | TSizeOfStr _ | TAlignOf _ | TAlignOfE _
      | Tlambda _ | TDataCons _ | Tbase_addr _ | TBinOp _ | TUnOp _
      | Tblock_length _ | TCoerce _ | TCoerceE _ | TUpdate _
      | Ttypeof _ | Ttype _ | Tlet _ | Toffset _ -> assert false
    in
    let zone idts =
      List.map Logic_const.new_identified_term (term idts.it_content)
    in
    let assign (z,froms) =
      let zl = zone z in
      let froms = 
        match froms with
            FromAny -> froms
          | From l -> From (List.flatten (List.map zone l))
      in
      List.map (fun z -> z, froms) zl
    in
    let assigns =
      (match b.b_assigns with
          WritesAny -> WritesAny
        | Writes l -> Writes (List.flatten (List.map assign l)))
    in
(*    Format.eprintf "[Norm.vbehavior] b_allocation = ";
    begin
      match b.b_allocation with
        | FreeAllocAny ->
            Format.eprintf "FreeAllocAny@."
        | FreeAlloc(l1,l2) ->
            Format.eprintf "FreeAlloc(%d,%d)@." (List.length l1) (List.length l2)
    end;
*)
    let new_bhv =
      Cil.mk_behavior
        ~name:b.b_name
        ~requires:b.b_requires
        ~assumes:b.b_assumes
        ~post_cond:b.b_post_cond
        ~assigns:assigns
        ~allocation:(Some b.b_allocation)
        ()
    in
    ChangeDoChildrenPost(new_bhv,fun x -> x)

  method vstmt_aux s = match s.skind with
    | Return(Some e,loc) ->
        (* Type of [e] has not been changed by retyping formals and return. *)
        if isStructOrUnionType (typeOf e) then
(*           match e with *)
(*             | Lval lv -> *)
(*                 let skind = Return(Some(Cabs2cil.mkAddrOfAndMark lv),loc) in *)
(*                 ChangeTo { s with skind = skind; } *)
(*             | _ -> assert false (\* Should not be possible *\) *)
          let lv = Var(the !return_var),NoOffset in
          let ret =
            mkStmt (Return(Some(Cabs2cil.mkAddrOfAndMark loc lv),loc))
          in
          let assigns = expand_assign lv e (typeOf e) loc in
          let assigns = List.map (fun i -> mkStmt(Instr i)) assigns in
          let block = Block (mkBlock (assigns @ [ret])) in
          ChangeTo { s with skind = block }
        else SkipChildren
    | _ -> DoChildren

  method vinst =
    function
      | Set(lv,e,loc) ->
          (* Type of [e] has not been changed by retyping formals and return. *)
          if isStructOrUnionType (typeOf e) then
            ChangeTo (expand_assign lv e (typeOf e) loc)
          else SkipChildren
      | Call(lvo,callee,args,loc) ->
          let args = List.map (fun arg ->
            (* Type of [arg] has not been changed. *)
            if isStructOrUnionType (typeOf arg) then
              match arg.enode with
              | Lval lv -> Cabs2cil.mkAddrOfAndMark loc lv
              | _ -> assert false (* Should not be possible *)
            else arg
          ) args in
          begin match lvo with
            | None ->
                (* TODO: free memory for structure return, even if not used.
                   Check that no temporary is added in every case, which would
                   make treatment here useless. *)
                let call = Call (lvo, callee, args, loc) in
                ChangeTo [call]
            | Some lv ->
                (* Type of [lv] has not been changed. *)
                let lvty = typeOfLval lv in
                if isStructOrUnionType lvty then
                  let tmpv = 
                    makeTempVar
                      (Extlib.the self#current_func) (mkTRef lvty "Norm.vinst")
                  in
                  let tmplv = Var tmpv, NoOffset in
                  let call = Call(Some tmplv,callee,args,loc) in
                  let deref =
                    new_exp ~loc
                      (Lval
                         (mkMem
                            (new_exp ~loc (Lval(Var tmpv,NoOffset))) NoOffset))
                  in
                  let assign = mkassign lv deref loc in
                  let free = mkfree tmpv loc in
                  ChangeTo [call;assign;free]
                else
                  let call = Call(lvo,callee,args,loc) in
                  ChangeTo [call]
          end
      | Asm _ | Skip _ -> SkipChildren
      | Code_annot _ -> assert false

  method vterm_lval tlv =
    ChangeDoChildrenPost (tlv, postaction_term_lval)

  method vterm t =
    (* Renormalize the term tree. *)
    let postaction t =
      match t.term_node with
        | TAddrOf(TMem t,TNoOffset) -> t
        | _ -> t
    in
    ChangeDoChildrenPost (t, postaction)

end

let expand_struct_assign file =
  let visitor = new expandStructAssign () in
  visitFramacFile (visit_and_push_statements_visitor visitor) file


(*****************************************************************************)
(* Retype variables of structure type.                                       *)
(*****************************************************************************)

(* DO NOT CHANGE neither formal parameters nor return type of functions.
 *
 * global variable:
 * - change type to reference to structure
 * - prepend allocation in [globinit] function
 * - changes left-values to reflect new type
 * local variable:
 * - change type to reference to structure
 * - prepend allocation at function entry
 * - TODO: postpend release at function exit
 * - changes left-values to reflect new type
 *)

class retypeStructVariables =

  let varset = ref Cil_datatype.Varinfo.Set.empty in
  let lvarset = ref Cil_datatype.Logic_var.Set.empty in

  let postaction_lval (host,off) =
    let host = match host with
      | Var v ->
          if Cil_datatype.Varinfo.Set.mem v !varset then
            Mem(mkInfo(new_exp ~loc:(Cil_const.CurrentLoc.get())
                         (Lval(Var v,NoOffset))))
          else
            Var v
      | Mem _e -> host
    in
    host, off
  in
  let postaction_tlval (host,off) =
    let add_deref host v =
      TMem(mkterm (TLval (host,TNoOffset)) v.lv_type
             (Cil_const.CurrentLoc.get()))
    in
    let host = match host with
      | TVar v ->
          if Cil_datatype.Logic_var.Set.mem v !lvarset then
            add_deref host v
          else
            Extlib.may_map
              (fun cv ->
                 if Cil_datatype.Varinfo.Set.mem cv !varset then
                   add_deref host v
                 else host
              ) ~dft:host v.lv_origin
      | TMem _ | TResult _ -> host
    in
    host, off
  in
object(self)

  inherit Visitor.frama_c_inplace

  method vvdec v =
    if isStructOrUnionType v.vtype && not v.vformal then
      begin
        v.vtype <- mkTRef v.vtype "Norm.vvdec";
        varset := Cil_datatype.Varinfo.Set.add v !varset
      end;
    DoChildren

  method vquantifiers vl =
    List.iter (fun v ->
                 (* Only iterate on logic variable with C type *)
                 if app_term_type (fun _ -> true) false v.lv_type then
                   match v.lv_origin with
                     | None -> ()
                     | Some v -> ignore (self#vvdec v)
                 else ()
              ) vl;
    DoChildren

  method vlogic_var_decl v =
    let newty =
      app_term_type
        (fun ty ->
           Ctype (if isStructOrUnionType ty then mkTRef ty "Norm.vlogic_var_decl" else ty))
        v.lv_type v.lv_type
    in
    v.lv_type <- newty;
    DoChildren

  method vglob_aux = function
    | GVar (_,_,_) as g ->
        let postaction = function
          | [GVar (v,_,_)] ->
              if Cil_datatype.Varinfo.Set.mem v !varset then
                (* Allocate memory for new reference variable *)
(* Disabled, see BTS 0284
                let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
                attach_globinit ast;
*)
                (* Define a global validity invariant *)
                let p =
                  Logic_const.pvalid_range
                    ~loc:v.vdecl
                    (label_here,
                     variable_term v.vdecl (cvar_to_lvar v),
                     constant_term v.vdecl Integer.zero,
                     constant_term v.vdecl Integer.zero)
                in
                let globinv =
		  Cil_const.make_logic_info (unique_logic_name ("valid_" ^ v.vname))
		in
                globinv.l_labels <- [ label_here ];
                globinv.l_body <- LBpred p;
                attach_globaction
		  (fun () -> Logic_utils.add_logic_function globinv);
                [g; GAnnot(Dinvariant (globinv,v.vdecl),v.vdecl)]
              else [g]
          | _ -> assert false
        in
        ChangeDoChildrenPost ([g], postaction)
    | GVarDecl _ | GFun _ | GAnnot _ -> DoChildren
    | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method vfunc f =
    (* First change type of local structure variables *)
    List.iter (ignore $ Cil.visitCilVarDecl (self:>Cil.cilVisitor)) f.slocals;
    List.iter (ignore $ Cil.visitCilVarDecl (self:>Cil.cilVisitor)) f.sformals;
    (* Then allocate/deallocate memory for those that need it *)
    List.iter (fun v ->
      if Cil_datatype.Varinfo.Set.mem v !varset then
        let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
        add_pending_statement ~beginning:true ast;
        (* do not deallocate variable used in returning a structure *)
        if not (Cil_datatype.Varinfo.Hashtbl.mem return_vars v) then
          let fst = mkfree_statement v v.vdecl in
          add_pending_statement ~beginning:false fst
    ) f.slocals;
    DoChildren

  method vlval lv =
    ChangeDoChildrenPost (lv, postaction_lval)

  method vterm_lval lv = ChangeDoChildrenPost(lv, postaction_tlval)

  method vexpr e =
    (* Renormalize the expression tree. *)
    let postaction e = match e.enode with
      | AddrOf(Mem e,NoOffset) -> e
      | _ -> e
    in
    ChangeDoChildrenPost (e, postaction)

  method vterm t =
    (* Renormalize the term tree. *)
    let postaction t =
      match t.term_node with
        | TAddrOf(TMem t,TNoOffset) -> t
        | _ -> t
    in
    ChangeDoChildrenPost (t, postaction)

end

let retype_struct_variables file =
  let visitor = new retypeStructVariables in
  visit_and_push_statements visit_and_update_globals visitor file


(*****************************************************************************)
(* Retype variables and fields whose address is taken.                       *)
(*****************************************************************************)

(* global variable:
 * - change type from [t] to [t*]
 * - prepend allocation in [globinit] function
 * local variable:
 * - change type from [t] to [t*]
 * - prepend allocation at function entry
 * - TODO: postpend release at function exit
 * formal parameter:
 * - make it a local variable, with previous treatment
 * - replace by a new parameter with same type
 * - prepend initialisation at function entry, after allocation
 * - TODO: decide whether formal parameter address can be taken in
 *   annotations. Currently, if address only taken in annotations,
 *   [vaddrof] would not be set. Plus there is no easy means of translating
 *   such annotation to Jessie.
 * field:
 * - change type from [t] to [t*]
 * - TODO: allocation/release
 *)
class retypeAddressTaken =

  let varset = ref Cil_datatype.Varinfo.Set.empty in
  let lvarset = ref Cil_datatype.Logic_var.Set.empty in
  let fieldset = ref Cil_datatype.Fieldinfo.Set.empty in

  let retypable_var v =
    v.vaddrof
    && not (isArrayType v.vtype)
    && not (is_reference_type v.vtype)
  in
  let retypable_lvar v =
    match v.lv_origin with None -> false | Some v -> retypable_var v
  in
  (* Only retype fields with base/pointer type, because fields of
   * struct/union type will be retyped in any case later on.
   *)
  let retypable_field fi =
    fi.faddrof
    && not (is_reference_type fi.ftype)
    && not (isArrayType fi.ftype)
    && not (isStructOrUnionType fi.ftype)
  in
  let retype_var v =
    if retypable_var v then
      begin
        v.vtype <- mkTRef v.vtype "Norm.retype_var";
        assert (isPointerType v.vtype);
        varset := Cil_datatype.Varinfo.Set.add v !varset
      end
  in
  let retype_lvar v =
    if retypable_lvar v then begin
      v.lv_type <- Ctype (force_app_term_type (fun x -> mkTRef x "Norm.retyp_lvar") v.lv_type);
      lvarset := Cil_datatype.Logic_var.Set.add v !lvarset
    end
  in
  let retype_field fi =
    if retypable_field fi then
      begin
        fi.ftype <- mkTRef fi.ftype "Norm.retype_field";
        assert (isPointerType fi.ftype);
        fieldset := Cil_datatype.Fieldinfo.Set.add fi !fieldset
      end
  in

  let postaction_lval (host,off) =
    let host = match host with
      | Var v ->
          if Cil_datatype.Varinfo.Set.mem v !varset then
            begin
              assert (isPointerType v.vtype);
              Mem(mkInfo
                    (new_exp ~loc:(Cil_const.CurrentLoc.get())
                       (Lval(Var v,NoOffset))))
            end
          else host
      | Mem _e -> host
    in
    (* Field retyped can only appear as the last offset, as it is of
     * base/pointer type.
     *)
    match lastOffset off with
    | Field(fi,_) ->
        if Cil_datatype.Fieldinfo.Set.mem fi !fieldset then
          (assert (isPointerType fi.ftype);
          mkMem
            (mkInfo
               (new_exp
                  ~loc:(Cil_const.CurrentLoc.get())
                  (Lval(host,off)))) NoOffset)
        else
          host,off
    | _ ->
        host,off
  in

  let postaction_tlval (host,off) =
    let add_deref host ty =
      force_app_term_type (fun ty -> assert (isPointerType ty)) ty;
      TMem(mkterm (TLval (host,TNoOffset)) ty (Cil_const.CurrentLoc.get()))
    in
    let host = match host with
      | TVar v ->
          if Cil_datatype.Logic_var.Set.mem v !lvarset then
            add_deref host v.lv_type
          else
            Extlib.may_map
              (fun cv ->
                 if Cil_datatype.Varinfo.Set.mem cv !varset then
                   add_deref host (Ctype cv.vtype)
                 else host
              ) ~dft:host v.lv_origin
      | TResult _ | TMem _ -> host
    in match Logic_const.lastTermOffset off with
      | TField (fi,_) ->
          if Cil_datatype.Fieldinfo.Set.mem fi !fieldset then
            (TMem
               (Logic_utils.mk_dummy_term (TLval(host,off)) fi.ftype),TNoOffset)
          else host,off
      | TModel _ | TIndex _ | TNoOffset -> host,off
  in
  let postaction_expr e = match e.enode with
    | AddrOf(Var _v,NoOffset) ->
        unsupported "cannot take address of a function"
          (* Host should have been turned into [Mem] *)
    | AddrOf(Mem e1,NoOffset) ->
        e1
    | AddrOf(_host,off) ->
        begin match lastOffset off with
          | Field(fi,_) ->
              if Cil_datatype.Fieldinfo.Set.mem fi !fieldset then
                (* Host should have been turned into [Mem], with NoOffset *)
                assert false
              else
                e
          | Index _ -> e
          | NoOffset -> assert false (* Should be unreachable *)
        end
    | _ -> e
  in
  let postaction_term t = match t.term_node with
    | TAddrOf((TVar _ | TResult _), TNoOffset) -> assert false
    | TAddrOf(TMem t1,TNoOffset) -> t1
    | TAddrOf(_,off) ->
        begin match Logic_const.lastTermOffset off with
          | TField(fi,_) ->
              if Cil_datatype.Fieldinfo.Set.mem fi !fieldset then assert false
              else t
          | TModel _ -> Common.unsupported "Model field"
          | TIndex _ -> t
          | TNoOffset -> assert false (*unreachable*)
        end
    | _ -> t
  in
  let varpairs : (varinfo * varinfo) list ref = ref [] in
  let in_funspec = ref false in
object

  inherit Visitor.frama_c_inplace

  method vglob_aux = function
    | GVar(v,_,_) ->
        if retypable_var v then
          begin
            retype_var v;
(* Disabled, see BTS 0284
            let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
            attach_globinit ast
*)
          end;
        SkipChildren
    | GVarDecl (_,v,_) ->
        (* No problem with calling [retype_var] more than once, since
           subsequent calls do nothing on reference type. *)
        if not (isFunctionType v.vtype || v.vdefined) then retype_var v;
        SkipChildren
    | GFun _ -> DoChildren
    | GAnnot _ -> DoChildren
    | GCompTag(compinfo,_loc) ->
        List.iter retype_field compinfo.cfields;
        SkipChildren
    | GType _ | GCompTagDecl _ | GEnumTagDecl _ | GEnumTag _
    | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method vfunc f =
    (* Change types before code. *)
    let formals,locals,pairs =
      List.fold_right (fun v (fl,ll,pl) ->
        if retypable_var v then
          let newv = copyVarinfo v ("v_" ^ v.vname) in
          newv.vaddrof <- false;
          v.vformal <- false;
          (newv::fl,v::ll,(v,newv)::pl)
        else (v::fl,ll,pl)
      ) f.sformals ([],[],[])
    in

    varpairs := pairs;
    setFormals f formals;
    f.slocals <- locals @ f.slocals;
    List.iter retype_var f.slocals;

    List.iter (fun v ->
      (* allocate/deallocate locals *)
      if Cil_datatype.Varinfo.Set.mem v !varset then
        begin
          let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
          add_pending_statement ~beginning:true ast;
          (* do not deallocate variable used in returning a structure *)
          if not (Cil_datatype.Varinfo.Hashtbl.mem return_vars v) then
            let fst = mkfree_statement v v.vdecl in
            add_pending_statement ~beginning:false fst
        end;
      (* allocate/deallocate formals *)
      begin try
        let loc = v.vdecl in
        (* [varpairs] holds pairs of (local,formal) to initialize due to
         * the transformation for formals whose address is taken.
         *)
        let fv = List.assoc v !varpairs in
        let lhs = mkMem (new_exp ~loc (Lval(Var v,NoOffset))) NoOffset in
        let rhs = new_exp ~loc (Lval(Var fv,NoOffset)) in
        let assign = mkassign_statement lhs rhs loc in
        add_pending_statement ~beginning:true assign
      with Not_found -> () end
    ) f.slocals;
    DoChildren

  method vspec _ =
    in_funspec := true;
    DoChildrenPost (fun x -> in_funspec := false; x)

  method vlogic_var_use v =
    if !in_funspec then
      match v.lv_origin with
        | None -> SkipChildren
        | Some cv ->
            try
              let fv = List.assoc cv !varpairs in
              ChangeTo (cvar_to_lvar fv)
            with Not_found -> SkipChildren
    else
      begin
        if retypable_lvar v then retype_lvar v;
        DoChildren
      end

  method vlogic_var_decl v = if retypable_lvar v then retype_lvar v; DoChildren

  method vlval lv = ChangeDoChildrenPost (lv, postaction_lval)

  method vterm_lval lv = ChangeDoChildrenPost (lv, postaction_tlval)

  method vexpr e = ChangeDoChildrenPost(e, postaction_expr)

  method vterm t = ChangeDoChildrenPost(t,postaction_term)

end

let retype_address_taken file =
  let visitor = new retypeAddressTaken in
  visit_and_push_statements visit_and_update_globals visitor file


(*****************************************************************************)
(* Retype fields of type structure and array.                                *)
(*****************************************************************************)

(* We translate C left-values so that they stick to the Jessie semantics for
 * left-values. E.g., a C left-value
 *     s.t.i
 * which is translated in CIL as
 *     Var s, Field(t, Field(i, NoOffset))
 * is translated as
 *     Mem (Mem s, Field(t, NoOffset)), Field(i, NoOffset)
 * so that it is the same as the C left-value
 *     s->t->i
 *
 * Introduce reference at each structure subfield.
 * Does not modify union fields on purpose : union should first be translated
 * into inheritance before [retypeFields] is called again.
 *)
class retypeFields =

  let field_to_array_type : typ Cil_datatype.Fieldinfo.Hashtbl.t = Cil_datatype.Fieldinfo.Hashtbl.create 0 in

  let postaction_lval (host,off) =
    let rec offset_list = function
      | NoOffset -> []
      | Field (fi,off) ->
          (Field (fi, NoOffset)) :: offset_list off
      | Index (e, Field (fi,off)) ->
          (Index (e, Field (fi, NoOffset))) :: offset_list off
      | Index (_idx, NoOffset) as off -> [off]
      | Index (idx, (Index _ as off)) ->
          assert (not !flatten_multi_dim_array);
          Index(idx,NoOffset) :: offset_list off
    in
    let rec apply_lift_offset = function
      | Field (fi,roff) ->
          begin try
            let ty = Cil_datatype.Fieldinfo.Hashtbl.find field_to_array_type fi in
            let roff = apply_lift_offset (lift_offset ty roff) in
            Field (fi,roff)
          with Not_found ->
            let roff = apply_lift_offset roff in
            Field (fi,roff)
          end
      | Index (idx,roff) ->
          let roff = apply_lift_offset roff in
          Index (idx,roff)
      | NoOffset -> NoOffset
    in
    let off =
      if !flatten_multi_dim_array then apply_lift_offset off else off
    in
    (* [initlv] : topmost lval
     * [initlist] : list of offsets to apply to topmost lval
     *)
    let initlv,initlist = match offset_list off with
      | [] -> (host, NoOffset), []
      | fstoff :: roff -> (host, fstoff), roff
    in
    List.fold_left
      (fun curlv -> function
         | NoOffset ->
             assert false (* should not occur *)
         | Field(_,_)
         | Index(_, Field (_,_))
         | Index(_, NoOffset) as nextoff ->
             Mem
               (mkInfo
                  (new_exp ~loc:(Cil_const.CurrentLoc.get()) (Lval curlv))),
             nextoff
         | Index (_, Index _) -> assert false
      ) initlv initlist
  in

  (* Renormalize the expression tree. *)
  let postaction_expr e = match e.enode with
    | AddrOf(Mem e,NoOffset) | StartOf(Mem e,NoOffset) -> e
    | AddrOf(Mem _e,Field(_fi,off) as lv)
    | StartOf(Mem _e,Field(_fi,off) as lv) ->
        assert (off = NoOffset);
        (* Only possibility is that field is of structure or union type,
         * otherwise [retype_address_taken] would have taken care of it.
         * Do not check it though, because type was modified in place.
         *)
        new_exp ~loc:e.eloc (Lval lv)
    | AddrOf(Mem e',Index(ie,NoOffset)) ->
        let ptrty = TPtr(typeOf e',[]) in
        new_exp ~loc:e.eloc (BinOp(PlusPI,e',ie,ptrty))
    | StartOf(Mem _e,Index(_ie,NoOffset) as lv) ->
        new_exp ~loc:e.eloc (Lval lv)
    | AddrOf(Mem _e,Index(_ie,Field(_,NoOffset)) as lv)
    | StartOf(Mem _e,Index(_ie,Field(_,NoOffset)) as lv) ->
        new_exp ~loc: e.eloc (Lval lv)
    | AddrOf(Mem _e,Index(_ie,_)) | StartOf(Mem _e,Index(_ie,_)) ->
        assert false
    | _ -> e
  in
object

  inherit Visitor.frama_c_inplace

  method vglob_aux = function
    | GCompTag (compinfo,_) ->
        let field fi =
          if isStructOrUnionType fi.ftype then
            fi.ftype <- mkTRef fi.ftype "Norm.vglob_aux(2)"
          else if isArrayType fi.ftype then
            begin
              Cil_datatype.Fieldinfo.Hashtbl.replace field_to_array_type fi fi.ftype;
              if not !flatten_multi_dim_array then
                fi.ftype <- reference_of_array fi.ftype
              else
(*                 if array_size fi.ftype > 0L then *)
                  let size = constant_expr (array_size fi.ftype) in
                  fi.ftype <- mkTRefArray(element_type fi.ftype,size,[])
(*                 else *)
(*                   (\* Array of zero size, e.g. in struct array hack. *\) *)
(*                   fi.ftype <- TPtr(element_type fi.ftype,[]) *)
            end
        in
        List.iter field compinfo.cfields;
        SkipChildren
    | GFun _ | GAnnot _ | GVar _ | GVarDecl _ -> DoChildren
    | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method vlval lv =
    ChangeDoChildrenPost (lv, postaction_lval)

  method vterm_lval =
    do_on_term_lval (None,Some postaction_lval)

  method vexpr e =
    ChangeDoChildrenPost(e, postaction_expr)

  method vterm =
    do_on_term (None,Some postaction_expr)

end

let retype_fields file =
  let visitor = new retypeFields in visitFramacFile visitor file


(*****************************************************************************)
(* Retype type tags.                                                         *)
(*****************************************************************************)

class retypeTypeTags =
object

  inherit Visitor.frama_c_inplace

  method vterm t = match t.term_node with
    | Ttype ty -> ChangeTo ({ t with term_node = Ttype(TPtr(ty,[])) })
    | _ -> DoChildren

end

let retype_type_tags file =
  let visitor = new retypeTypeTags in visitFramacFile visitor file

(*****************************************************************************)
(* Retype pointers to base types.                                            *)
(*****************************************************************************)

(* Retype pointer to base type T to pointer to struct S with:
 * - if T is [TVoid], no field in S
 * - otherwise, a single field of type T in S
 *)
class retypeBasePointer =

  (* Correspondance between a base type and its wrapper structure type *)
  let type_wrappers = Cil_datatype.Typ.Hashtbl.create 17 in
  (* Store which types are wrapper types *)
  let auto_type_wrappers = ref Cil_datatype.Typ.Set.empty in

  let is_wrapper_type ty = Cil_datatype.Typ.Set.mem ty !auto_type_wrappers in

  let new_wrapper_for_type_no_sharing ty =
    (* Choose name t_P for the wrapper and t_M for the field *)
    let name = type_name ty in
    let wrapper_name = name ^ "P" in
    let field_name = name ^ "M" in
    let compinfo =
      if isVoidType ty then mkStructEmpty wrapper_name
      else mkStructSingleton wrapper_name field_name ty
    in
    let tdef = GCompTag(compinfo,Cil_datatype.Location.unknown) in
    let tdecl = TComp(compinfo,empty_size_cache () ,[]) in
    attach_global tdef;
    tdef, tdecl
  in
object(self)

  (* Helper methods called on the [self] object *)

  method new_wrapper_for_type ty =
    (* Currently, do not make any difference between a pointer to const T
     * or volatile T and a pointer to T.
     *)
    let ty = typeRemoveAttributes ["const";"volatile"] (unrollType ty) in
    try
      Cil_datatype.Typ.Hashtbl.find type_wrappers ty
    with Not_found ->
      (* Construct a new wrapper for this type *)
      let wrapper_def,wrapper_type = new_wrapper_for_type_no_sharing ty in
      Cil_datatype.Typ.Hashtbl.replace type_wrappers ty wrapper_type;
      auto_type_wrappers :=
        Cil_datatype.Typ.Set.add wrapper_type !auto_type_wrappers;
      (* Treat newly constructed type *)
      let store_current_global = !currentGlobal in
      ignore (Cil.visitCilGlobal (self:>Cil.cilVisitor) wrapper_def);
      currentGlobal := store_current_global;
      (* Return the wrapper type *)
      wrapper_type

  (* Performs the necessary in-place modifications to [ty] so that
   * the translation to Jessie is easy.
   * Returns [Some newty] if the modified type imposes adding a field
   * access to a dereference on an object of type [ty].
   * Returns [None] in all other cases, in particular for non-wrapper
   * types that are allowed as either type of variable or type of field.
   *)
  method private wrap_type_if_needed ty =
    match ty with
      | TPtr(_elemty,attr) ->
          (* Do not use [_elemty] directly but rather [pointed_type ty] in order
           * to get to the array element in references, i.e. pointers to arrays.
           *)
          let elemty = pointed_type ty in
          if is_wrapper_type elemty then
            Some ty
          else if isStructOrUnionType elemty then
            None (* Already in a suitable form for Jessie translation. *)
          else if is_array_reference_type ty then
            (* Do not lose the information that this type is a reference *)
            let size = constant_expr (Integer.of_int64 (reference_size ty)) in
            assert (not (!flatten_multi_dim_array && is_reference_type elemty));
            Some(mkTRefArray(self#new_wrapper_for_type elemty,size,[]))
          else if is_reference_type ty then
            (* Do not lose the information that this type is a reference *)
            Some(mkTRef(self#new_wrapper_for_type elemty)"Norm.private wrap_type_if_needed")
          else
            (* Here is the case where a transformation is needed *)
            Some(TPtr(self#new_wrapper_for_type elemty,attr))
      | TArray (_,len,size,attr) ->
          (*[VP-20100826] Can happen in case of logic term translation *)
          let elemty = element_type ty in
          if is_wrapper_type elemty then Some ty
          else if isStructOrUnionType elemty then None
          else Some (TArray(self#new_wrapper_for_type elemty,len,size,attr))
      | TFun _ -> None
      | TNamed(typeinfo,_attr) ->
          begin match self#wrap_type_if_needed typeinfo.ttype with
            | Some newtyp ->
                typeinfo.ttype <- newtyp;
                Some ty
            | None -> None
          end
      | TComp(compinfo,_,_) ->
          let field fi =
            match self#wrap_type_if_needed fi.ftype with
              | Some newtyp ->
                  fi.ftype <- newtyp
              | None -> ()
          in
          List.iter field compinfo.cfields;
          None
      | TVoid _ | TInt _ | TFloat _ | TEnum _ | TBuiltin_va_list _ -> None

  method private postaction_lval lv =
    match lv with
      | Var _, NoOffset -> lv
      | Var _, _ ->
          unsupported "cannot handle this lvalue: %a" Printer.pp_lval lv
      | Mem e, NoOffset ->
          begin match self#wrap_type_if_needed (typeOf e) with
            | Some newtyp ->
                let newfi = get_unique_field (pointed_type newtyp) in
                let newlv = Mem e, Field (newfi, NoOffset) in
                (* Check new left-value is well-typed. *)
(*                 begin try ignore (typeOfLval newlv) with _ -> assert false end; *)
                newlv
            | None -> lv
          end
      | Mem e, (Index(ie,_) as off) ->
          if is_last_offset off then
            match self#wrap_type_if_needed (typeOf e) with
              | Some newtyp ->
                  let newfi = get_unique_field (pointed_type newtyp) in
                  let newlv =
                    if Cil.isArrayType (direct_pointed_type newtyp) then
                      lv
                    else (* The array has been directly decayed into a pointer
                            Use pointer arithmetic instead of index. *)
                      (Mem
                         (new_exp ~loc:e.eloc
                            (BinOp(PlusPI,e,ie,newtyp))),
                       NoOffset)
                  in
                  let newlv = addOffsetLval (Field (newfi, NoOffset)) newlv in
                  newlv
              | None -> lv
          else lv
      | Mem _, Field _ -> lv

  (* Usual methods in visitor interface. *)

  inherit Visitor.frama_c_inplace

  method vfile _ =
    Common.struct_type_for_void := self#new_wrapper_for_type voidType;
    DoChildren

  method vtype ty =
    let ty = match self#wrap_type_if_needed ty with
      | Some newty -> newty
      | None -> ty
    in
    if isFunctionType ty then
      (* Applies changes in particular to parameter types in function types. *)
      ChangeDoChildrenPost (ty, fun x -> x)
    else
      ChangeTo ty

  method vglob_aux =
    let retype_return v =
      let retyp = getReturnType v.vtype in
      let newtyp = Cil.visitCilType (self:>Cil.cilVisitor) retyp in
      if newtyp != retyp then setReturnTypeVI v newtyp
    in
    function
      | GType (typeinfo, _) ->
          ignore (self#wrap_type_if_needed (TNamed (typeinfo, [])));
          SkipChildren
      | GCompTag (compinfo, _) ->
          ignore (self#wrap_type_if_needed (TComp (compinfo, empty_size_cache (), [])));
          SkipChildren
      | GFun (f, _) ->
          retype_return f.svar;
          DoChildren
      | GVarDecl (_, v, _) ->
          if isFunctionType v.vtype && not v.vdefined then
            retype_return v;
          DoChildren
      | GVar _
      | GAnnot _ -> DoChildren
      | GCompTagDecl _ | GEnumTag _ | GEnumTagDecl _
      | GAsm _ | GPragma _ | GText _  -> SkipChildren

  method vlval lv =
    ChangeDoChildrenPost (lv, self#postaction_lval)

  method vterm_lval t =
    do_on_term_lval (None,Some self#postaction_lval) t

end

let retype_base_pointer file =
  let visitor = new retypeBasePointer in
  visit_and_update_globals (visitor :> frama_c_visitor) file


(*****************************************************************************)
(* Remove useless casts.                                                     *)
(*****************************************************************************)

class removeUselessCasts =
  let preaction_expr etop =
    match (stripInfo etop).enode with
      | CastE(ty,e) ->
          let ety = typeOf e in
          if isPointerType ty && isPointerType ety &&
            Cil_datatype.Typ.equal
              (Cil.typeDeepDropAttributes
                 ["const"; "volatile"] (pointed_type ty))
              (Cil.typeDeepDropAttributes
                 ["const"; "volatile"] (pointed_type ety))
          then e
          else etop
      | _ -> etop
  in
  let preaction_term term =
    match term.term_node with
      | TCastE(ty,t) ->
          if isPointerType ty && Logic_utils.isLogicPointer t then
            (* Ignore type qualifiers *)
            let pty = Cil.typeDeepDropAllAttributes (pointed_type ty) in
            let ptty =
              match t.term_type with
                  Ctype tty ->
                    if isPointerType tty then pointed_type tty 
                    else element_type tty
                | ty -> fatal "Not a pointer type '%a'"
                  Cil_datatype.Logic_type.pretty ty
            in
            if Cil_datatype.Typ.equal pty ptty then
              if Logic_utils.isLogicPointerType t.term_type then t
              else
                (match t.term_node with
                   | TLval lv -> Logic_const.term (TStartOf lv) (Ctype ty)
                   | TStartOf _ -> t
                   | _ ->
                       fatal
                         "Unexpected array expression casted into pointer: %a"
                         Cil_datatype.Term.pretty t
                )
            else term
          else term
      | _ -> term
  in
object

  inherit Visitor.frama_c_inplace

  method vexpr e = ChangeDoChildrenPost (preaction_expr e, fun x -> x)

  method vterm t = ChangeDoChildrenPost (preaction_term t, fun x -> x)

end

let remove_useless_casts file =
  let visitor = new removeUselessCasts in visitFramacFile visitor file


(*****************************************************************************)
(* Translate union fields into structures                                    *)
(*****************************************************************************)

let generated_union_types = Cil_datatype.Typ.Hashtbl.create 0

class translateUnions =
  let field_to_equiv_type : typ Cil_datatype.Fieldinfo.Hashtbl.t
      = Cil_datatype.Fieldinfo.Hashtbl.create 0
  in
  let new_field_type fi =
    let tname = unique_name (fi.fname ^ "P") in
    let fname = unique_name (fi.fname ^ "M") in
    let padding = the fi.fpadding_in_bits in
    let mcomp =
      mkStructSingleton ~padding tname fname fi.ftype in
    let tdef = GCompTag (mcomp, CurrentLoc.get ()) in
    let tdecl = TComp (mcomp, empty_size_cache (), []) in
    Cil_datatype.Typ.Hashtbl.add generated_union_types tdecl ();
    Cil_datatype.Fieldinfo.Hashtbl.add field_to_equiv_type fi tdecl;
    fi.ftype <- tdecl;
    tdef
  in

  let postaction_offset = function
    | Field(fi,off) as off' ->
        begin try
          let ty = Cil_datatype.Fieldinfo.Hashtbl.find field_to_equiv_type fi in
          let newfi = get_unique_field ty in
          Field(fi,Field(newfi,off))
        with Not_found -> off' end
    | off -> off
  in
object

  inherit Visitor.frama_c_inplace

  method vglob_aux = function
    | GCompTag (compinfo,_) as g when not compinfo.cstruct ->
        let fields = compinfo.cfields in
        let field fi = new_field_type fi in
        let fty = List.map field fields in
        ChangeTo (g::fty)
    | GFun _ | GAnnot _ | GVar _ | GVarDecl _ -> DoChildren
    | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method voffs off =
    ChangeDoChildrenPost(off,postaction_offset)

  method vterm_offset =
    do_on_term_offset (None, Some postaction_offset)

end

let translate_unions file =
  let visitor = new translateUnions in visitFramacFile visitor file

(*****************************************************************************)
(* Remove array address.                                                     *)
(*****************************************************************************)

class removeArrayAddress =
object

  inherit Visitor.frama_c_inplace

  method vexpr e =
    let preaction e = match e.enode with
      | AddrOf(Mem ptre,Index(ie,NoOffset)) ->
          let ptrty = typeOf e in
          new_exp ~loc:e.eloc (BinOp (PlusPI, ptre, ie, ptrty))
      | _ -> e
    in
    ChangeDoChildrenPost (preaction e, fun x -> x)

  method vterm t =
    let preaction t = match t.term_node with
      | TAddrOf(TMem ptrt,TIndex(it,TNoOffset)) ->
          { t with term_node = TBinOp (PlusPI, ptrt, it); }
      | _ -> t
    in
    ChangeDoChildrenPost (preaction t, fun x -> x)

  (* TODO: translate to add tsets easily *)

end

let remove_array_address file =
  let visitor = new removeArrayAddress in
  visitFramacFile visitor file


(*****************************************************************************)
(* Normalize the C file for Jessie translation.                              *)
(*****************************************************************************)

let normalize file =
  if checking then check_types file;
  (* Retype variables of array type. *)
  (* order: before [expand_struct_assign] and any other pass which calls
     [typeOf], because "t[i]" with [StartOf] if type of "t" is "int t[a][b]"
     is not typed correctly by Cil (raises error StartOf on non-array type).
     See, e.g., example array_addr.c. *)
  Jessie_options.debug "Retype variables of array type";
  retype_array_variables file;
  if checking then check_types file;
  (* Retype logic functions/predicates with structure parameters or return. *)
  Jessie_options.debug "Retype logic functions/predicates";
  retype_logic_functions file;
  if checking then check_types file;
  (* Expand structure copying through parameter, return or assignment. *)
  (* order: before [retype_address_taken], before [retype_struct_variables] *)
  Jessie_options.debug "Expand structure copying";
  expand_struct_assign file;
  if checking then check_types file;
  (* Retype variables of structure type. *)
  Jessie_options.debug "Retype variables of structure type";
  retype_struct_variables file;
  if checking then check_types file;
  (* Retype variables and fields whose address is taken. *)
  (* order: after [retype_struct_variables] *)
  Jessie_options.debug "Retype variables and fields whose address is taken";
  retype_address_taken file;
  if checking then check_types file;
  (* Expand structure copying through assignment. *)
  (* Needed because sequence [expand_struct_assign; retype_struct_variables;
     retype_address_taken] may recreate structure assignments. *)
  (* order: after [retype_address_taken] *)
  Jessie_options.debug "Expand structure copying through assignment";
  expand_struct_assign file;
  if checking then check_types file;
  (* Translate union fields into structures. *)
  Jessie_options.debug "Translate union fields into structures";
  translate_unions file;
  if checking then check_types file;
  (* Retype fields of type structure and array. *)
  (* order: after [expand_struct_assign] and [retype_address_taken]
   * before [translate_unions] *)
  Jessie_options.debug "Retype fields of type structure and array";
  retype_fields file;
  if checking then check_types file;
  (* Retype fields of type structure and array. *)
  (* order: after [translate_unions] *)
  Jessie_options.debug "Retype fields of type structure and array";
  retype_fields file;
  if checking then check_types file;
  (* Remove array address. *)
  (* order: before [retype_base_pointer] *)
  Jessie_options.debug "Remove array address";
  remove_array_address file;
  if checking then check_types file;
  (* Retype type tags. *)
  (* order: before [retype_base_pointer] *)
  Jessie_options.debug "Retype type tags";
  retype_type_tags file;
  if checking then check_types file;
  (* Retype pointers to base types. *)
  (* order: after [retype_fields] *)
  Jessie_options.debug "Retype pointers to base types";
  retype_base_pointer file;
  if checking then check_types file;
  (* Remove useless casts. *)
  Jessie_options.debug "Remove useless casts";
  remove_useless_casts file;
  if checking then check_types file;

(*
Local Variables:
compile-command: "make -C .."
End:
*)
