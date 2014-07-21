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


(* TODO:
 *
 *- In both retyping phases that add a level of indirection to locals:
 *     - Retype variables of structure type
 *     - Retype variables and fields whose address is taken
 *   If the returned value dereferences a local, take the returned value in
 *   a temporary before deallocating memory for the local variable and
 *   returning. Mostly an issue of consistency: since it is a local variable
 *   involved, it is retyped as a reference and no check is issued for
 *   validity of dereference.
 *   See ex roux3.c from Jessie test base.
 *   Thanks to Pierre Roux for noting this.
 *
 *)


(* Import from Cil *)
open Cil_types
open Cil
open Ast_info
open Extlib

open Visitor

(* Utility functions *)
open! Common

let label_here = LogicLabel (None, "Here")

(*****************************************************************************)
(* Retype variables of array type.                                           *)
(*****************************************************************************)

module Set_vi = Cil_datatype.Varinfo.Set
module Set_lv = Cil_datatype.Logic_var.Set
module Htbl_vi = Cil_datatype.Varinfo.Hashtbl
module Htbl_lv = Cil_datatype.Logic_var.Hashtbl

(* TODO: retype predicate \valid_index and \valid_range
 * E.g. in example array.c, "\valid_index(t, 1)" for "t" being typed as
 * "int t[3][3]", should be transformed into "\valid_range(t, 3, 5)".
 *)
class array_variables_retyping_visitor =

  (* Variables originally of array type *)
  let varset = ref Set_vi.empty in
  let lvarset = ref Set_lv.empty in

  (* Correspondance between variables and "straw" variables, that are used to
   * replace the variable after some changes have been made on the AST,
   * so that further exploration does not change it anymore. The "straw"
   * variables are replaced by regular one before returning the modified AST.
   *)
  let var_to_strawvar = Htbl_vi.create 17 in
  let strawvar_to_var = Htbl_vi.create 17 in
  let lvar_to_strawlvar = Htbl_lv.create 17 in
  let strawlvar_to_lvar = Htbl_lv.create 17 in

  (* Variables to allocate *)
  let allocvarset = ref Set_vi.empty in
  let alloclvarset = ref Set_lv.empty in

  (* Remember original array type even after variable modified *)
  let var_to_array_type : typ Htbl_vi.t = Htbl_vi.create 0 in
  let lvar_to_array_type = Htbl_lv.create 17 in

  (* As the rule would be reentrant, do not rely on the fact it is idempotent,
   * and rather change the variable into its "straw" counterpart, as it is
   * done in [preaction_expr]. Also make sure every top expression inside
   * a left-value is an [Info], so that terms that were converted to
   * expressions before treatment can be safely converted back.
   *)
  let preaction_lval (host, off as lv) =
    match host with
    | Var v when Set_vi.mem v !varset ->
      let strawv = Htbl_vi.find var_to_strawvar v in
      let loc = Cil_const.CurrentLoc.get () in
      let host = Mem (mkInfo @@ new_exp ~loc @@ Lval (Var strawv, NoOffset)) in
      let off = lift_offset (Htbl_vi.find var_to_array_type v) off in
      host, off
    | Var _ | Mem _ -> lv (* For terms, also corresponds to the case for Result *)
  in

  let postaction_lval (host, off as lv) =
    match host with
    | Var strawv ->
      begin try
        let v = Htbl_vi.find strawvar_to_var strawv in
        Var v, off
      with
      | Not_found -> lv
      end
    | Mem _ -> lv
  in

  let rec preaction_expr e =
    let loc = e.eloc in
    match e.enode with
    | StartOf (Var v, off) when Set_vi.mem v !varset ->
      let ty = Htbl_vi.find var_to_array_type v in
      let strawv = Htbl_vi.find var_to_strawvar v in
      begin match lift_offset ty off with
      | NoOffset -> new_exp ~loc @@ Lval (Var strawv, NoOffset)
      | Index (ie, NoOffset) ->
        let ptrty = TPtr (element_type ty, []) in
        new_exp ~loc @@ BinOp (PlusPI, new_exp ~loc @@ Lval (Var strawv, NoOffset), ie, ptrty)
      | Index _ | Field _ ->
        (* Field with address taken treated separately *)
        new_exp ~loc @@ StartOf (Mem (new_exp ~loc @@ Lval (Var strawv, NoOffset)), off)
      end
    | AddrOf (Var v, off) when Set_vi.mem v !varset ->
      let ty = Htbl_vi.find var_to_array_type v in
      let strawv = Htbl_vi.find var_to_strawvar v in
      begin match lift_offset ty off with
      | Index (ie, NoOffset) ->
        let ptrty = TPtr(element_type ty, []) in
        new_exp ~loc @@ BinOp (PlusPI, new_exp ~loc @@ Lval (Var strawv, NoOffset), ie, ptrty)
      | NoOffset -> unsupported "this instance of the address operator cannot be handled"
      | Index _ | Field _ ->
        (* Field with address taken treated separately *)
        new_exp ~loc @@ AddrOf (Mem (new_exp ~loc @@ Lval (Var strawv, NoOffset)), off)
      end
    | BinOp (PlusPI, e1, e2, opty) ->
      begin match (stripInfo e1).enode with
      | StartOf (Var v, off) when Set_vi.mem v !varset ->
        let ty = Htbl_vi.find var_to_array_type v in
        let e1 = preaction_expr e1 in
        let rec findtype ty =
          function
          | NoOffset -> ty
          | Index(_, roff) ->
            findtype (direct_element_type ty) roff
          | Field _ -> raise Not_found
        in
        (* Do not replace [v] by [strawv] here, as the sub-expression
         * [e1] should be treated first. Do it right away so that
         * the resulting AST is well-typed, which is crucial to apply
         * this on expressions obtained from terms.
         *)
        let ty = findtype ty off in
        let subty = direct_element_type ty in
        if isArrayType subty then
          let siz = array_size subty in
          let e2 = new_exp ~loc:e2.eloc @@ BinOp (Mult, e2, constant_expr siz, intType) in
          new_exp ~loc @@ BinOp (PlusPI, e1, e2, opty)
        else e
      | _ -> e
      end
    | _ -> e
  in
object(self)

  inherit frama_c_inplace

  method! vvdec v =
    if isArrayType v.vtype && not (Set_vi.mem v !varset) then begin
      if v.vformal then
        fatal "vvdec: unexpected array formal parameter (should have been retyped to pointer?): %s" v.vname;
      Htbl_vi.add var_to_array_type v v.vtype;
      let elemty = element_type v.vtype in
      (* Store information that variable was originally of array type *)
      varset := Set_vi.add v !varset;
      (* Change the variable type *)
      let newty =
        if Integer.(gt (array_size v.vtype) zero) then begin
          (* Change the type into "reference" type, that behaves almost like
           * a pointer, except validity is ensured.
           *)
          let size = constant_expr (array_size v.vtype) in
          (* Schedule for allocation *)
          allocvarset := Set_vi.add v !allocvarset;
          mkTRefArray (elemty, size, []);
        end else
          (* Plain pointer type to array with zero size *)
          TPtr (v.vtype, []);
      in
      attach_globaction (fun () -> v.vtype <- newty);
      (* Create a "straw" variable for this variable, with the correct type *)
      let strawv = makePseudoVar newty in
      Htbl_vi.add var_to_strawvar v strawv;
      Htbl_vi.add strawvar_to_var strawv v
    end;
    DoChildren

  method! vlogic_var_decl lv =
    if not (Htbl_lv.mem lvar_to_strawlvar lv) && app_term_type isArrayType false lv.lv_type then begin
      Htbl_lv.add lvar_to_array_type lv @@ force_app_term_type id lv.lv_type;
      let elemty = force_app_term_type element_type lv.lv_type in
      lvarset := Set_lv.add lv !lvarset;
      let newty =
        if Integer.(gt (force_app_term_type array_size lv.lv_type) zero) then begin
          let size = constant_expr (force_app_term_type array_size lv.lv_type) in
          alloclvarset := Set_lv.add lv !alloclvarset;
          mkTRefArray (elemty, size, [])
        end else
          TPtr (elemty, [])
      in
      attach_globaction (fun () -> lv.lv_type <- Ctype newty);
      let strawlv =
        match lv.lv_origin with
        | None -> make_temp_logic_var (Ctype newty)
        | Some v -> cvar_to_lvar (Htbl_vi.find var_to_strawvar v)
      in
      Htbl_lv.add lvar_to_strawlvar lv strawlv;
      Htbl_lv.add strawlvar_to_lvar strawlv lv
    end;
    DoChildren

  method! vglob_aux g =
    match g with
    | GVar (v, _init, _loc) ->
      (* Make sure variable declaration is treated before definition *)
      ignore @@ visitCilVarDecl (self :> cilVisitor) v;
      if Set_vi.mem v !allocvarset then
        (* Allocate memory for new reference variable *)
        let ty = Htbl_vi.find var_to_array_type v in
        let size = array_size ty in
        (* Disabled: anyway, it is useless to generate code for that,
         * a post-condition should be generated instead (bts0284)
         *  let elemty = element_type ty in
         *  let ast = mkalloc_array_statement v elemty (array_size ty) loc in
         *  attach_globinit ast;
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
        let globinv = Cil_const.make_logic_info (unique_logic_name ("valid_" ^ v.vname)) in
        globinv.l_labels <- [label_here];
        globinv.l_body <- LBpred p;
        attach_globaction (fun () -> Logic_utils.add_logic_function globinv);
        ChangeTo [g; GAnnot (Dinvariant (globinv, v.vdecl), v.vdecl)]
      else DoChildren
    | GVarDecl _ | GFun _ | GAnnot _ -> DoChildren
    | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method! vfunc f =
    (* First change type of local array variables *)
    List.iter (ignore % visitCilVarDecl (self :> cilVisitor)) f.slocals;
    List.iter (ignore % visitCilVarDecl (self :> cilVisitor)) f.sformals;
    (* Then allocate/deallocate memory for those that need it *)
    List.iter
      (fun v ->
        if Set_vi.mem v !allocvarset then
          let ty = Htbl_vi.find var_to_array_type v in
          let elemty = element_type ty in
          let ast = mkalloc_array_statement v elemty (Integer.to_int64 (array_size ty)) v.vdecl in
          add_pending_statement ~beginning:true ast;
          let fst = mkfree_statement v v.vdecl in
          add_pending_statement ~beginning:false fst)
      f.slocals;
    DoChildren

  method! vlval lv = ChangeDoChildrenPost (preaction_lval lv, postaction_lval)

  method! vterm_lval lv = do_on_term_lval (Some preaction_lval, Some postaction_lval) lv

  method! vexpr e = ChangeDoChildrenPost (preaction_expr e, id)

  method! vterm = do_on_term (Some preaction_expr, None)

end

let retype_array_variables file =
  (* Enforce the prototype of malloc to exist before visiting anything.
   * It might be useful for allocation pointers from arrays
   *)
  ignore (malloc_function ());
  ignore (free_function ());
  visit_and_push_statements visit_and_update_globals (new array_variables_retyping_visitor) file

(*****************************************************************************)
(* Retype logic functions/predicates with structure parameters or return.    *)
(*****************************************************************************)

let model_fields_table = Hashtbl.create 7

let model_fields compinfo =
  try Hashtbl.find model_fields_table compinfo.ckey with Not_found -> []

(* logic parameter:
 * - change parameter type to pointer to structure
 * - change uses of parameters in logical annotations
 * TODO: take care of logic variables introduced by let.
 *)
class logic_functions_retyping_visitor =

  let varset = ref Set_lv.empty in
  let this_name  = ref "" in
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

  let postaction_term_lval (host, off) =
    let host =
      match host with
      | TVar lv ->
        (* Oddly, "this" variable in type invariant is not declared
         * before use. Change its type on the fly.
         *)
        if !change_this_type && lv.lv_name = !this_name then
          var lv;
        if Set_lv.mem lv !varset then
          let tlval =
            mkterm (TLval (host, TNoOffset)) lv.lv_type (Cil_const.CurrentLoc.get ())
          in
          TMem tlval
        else host
      | TResult _ when !change_result_type ->
        begin match !new_result_type with
        | Ctype typ ->
          let tlval = Logic_const.tresult typ in
          TMem tlval
        | _ ->
          (* result type of C function must be a C type*)
          fatal
            "postaction_term_lval: result of a C function is not a C type %a"
            Printer.pp_logic_type !new_result_type
        end
      | TResult _ | TMem _ -> host
    in
    host, off
  in

  let preaction_term_arg arg =
    match arg.term_type with
    | Ctype ty when isStructOrUnionType ty ->
      begin match arg.term_node with
      | TLval lv ->
        (* Arguments translated under address here may
         * be translated back to dereference when treating
         * left-values. This is why we add a normalization
         * in [postaction_term]. *)
        { arg with
          term_node = TAddrOf lv;
          term_type = Ctype (mkTRef ty "Norm.vterm") }
      | _ ->
        (* Should not be possible *)
        fatal
          "preaction_term_arg: direct struct or union passed as something different from lvalue: %a"
          Printer.pp_term arg
      end
    | Ctype _ | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> arg
  in
object

  inherit frama_c_inplace

  method! vannotation =
    let return_type ty =
      change_result_type := false;
      match ty with
      | Ctype rt when isStructOrUnionType rt ->
        change_result_type := true;
        let ty = Ctype (mkTRef rt "Norm.vannotation") in
        new_result_type := ty;
        ty
      | Ctype _ | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> ty
    in
    let annot =
      function
      | Dfun_or_pred (li, loc) ->
        List.iter var li.l_profile;
        begin match li.l_type with
        | None -> DoChildren
        | Some rt ->
          let li' = { li with l_type = Some (return_type rt) }  in
          ChangeDoChildrenPost (Dfun_or_pred (li', loc), id)
        end
      | Dtype_annot (annot, loc) ->
        begin match (List.hd annot.l_profile).lv_type with
        | Ctype ty when isStructOrUnionType ty ->
          change_this_type := true;
          this_name := (List.hd annot.l_profile).lv_name;
          let annot = { annot with
                        l_profile = [{ (List.hd annot.l_profile) with
                                       lv_type = Ctype (mkTRef ty "Norm.annot, Dtype_annot")}]}
          in
          ChangeDoChildrenPost (Dtype_annot (annot, loc), fun x -> change_this_type := false; x)
        | Ctype _ | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> DoChildren
        end
      | Dtype _ | Dlemma _ | Dinvariant _ | Dvolatile _  -> DoChildren
      | Daxiomatic _ -> DoChildren (* FIXME: correct ? *)
      | Dmodel_annot (mi, _) ->
        begin match unrollType mi.mi_base_type with
        | TComp (ci, _, _) ->
          let l = try Hashtbl.find model_fields_table ci.ckey with Not_found -> [] in
          Hashtbl.replace model_fields_table ci.ckey (mi :: l)
        | _ -> unsupported "model field only on structures"
        end;
        DoChildren (* FIXME: correct ? *)
      | Dcustom_annot _ -> DoChildren (* FIXME: correct ? *)
    in
    annot

  method! vterm_lval tlv = ChangeDoChildrenPost (tlv, postaction_term_lval)

  method! vterm t =
    let preaction_term t =
      match t.term_node with
      | Tapp (callee, labels, args) ->
        let args = List.map preaction_term_arg args in
        { t with term_node = Tapp (callee, labels, args) }
      | _ -> t
    in
    (* Renormalize the term tree. *)
    let postaction_term t =
      match t.term_node with
      | TAddrOf(TMem t, TNoOffset) -> t
      | _ -> t
    in
    ChangeDoChildrenPost (preaction_term t, postaction_term)

  method! vpredicate =
    function
    | Papp (callee, labels, args) ->
      let args = List.map preaction_term_arg args in
      ChangeDoChildrenPost (Papp (callee, labels, args), id)
    | _ -> DoChildren

end

let retype_logic_functions file =
  visitFramacFile (new logic_functions_retyping_visitor) file

(*****************************************************************************)
(* Expand structure copying through parameter, return or assignment.         *)
(*****************************************************************************)

let return_vars = Htbl_vi.create 17

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
class struct_assign_expander () =

  let pairs = ref [] in
  let new_return_type = ref None in
  let return_var = ref None in

  let postaction_term_lval (host, off) =
    let host =
      match host with
      | TResult _ ->
        begin match !new_return_type with
        | None -> host
        | Some rt ->
          let tlval = Logic_const.tresult rt in
          TMem tlval
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
              mkterm (TLval (TVar newlv, TNoOffset)) (Ctype newv.vtype) (Cil_const.CurrentLoc.get ())
            in
            TMem tlval
          with
          | Not_found -> TVar v
        end
      | TMem _t -> host
    in
    host, off
  in

  let rec expand_assign lv e ty loc =
    match unrollType ty with
    | TComp (mcomp, _, _) ->
      let field fi =
        let newlv = addOffsetLval (Field(fi,NoOffset)) lv in
        let newe =
          match e.enode with
          | Lval elv ->
            new_exp ~loc:e.eloc @@ Lval (addOffsetLval (Field (fi, NoOffset)) elv)
          | _ ->
            (* Other possibilities like [CastE] should have been
               transformed at this point. *)
            fatal
              "unrecognized untransformed expression occurred during struct assignment expansion (for field %s): %a"
              fi.fname Printer.pp_exp e
        in
        expand_assign newlv newe fi.ftype loc
      in
      List.(flatten @@ map field mcomp.cfields)
    | TArray _ ->
      let elem i =
        let cste = constant_expr i in
        let newlv = addOffsetLval (Index (cste, NoOffset)) lv in
        let newe =
          match e.enode with
          | Lval elv ->
            new_exp ~loc:e.eloc @@ Lval (addOffsetLval (Index (cste, NoOffset)) elv)
          | _ ->
            (* Other possibilities like [CastE] should have been
               transformed at this point. *)
            fatal
              "unrecognized untransformed expression occurred during struct assignment expansion (for element %s): %a"
              (Integer.to_string i) Printer.pp_exp e
        in
        expand_assign newlv newe (direct_element_type ty) loc
      in
      let rec all_elem acc i =
        if Integer.(ge i zero) then
          all_elem (elem i @ acc) (Integer.pred i)
        else acc
      in
      if is_reference_type ty then
        fatal "array assignment expansion called on a reference type: %a: %a" Printer.pp_exp e Printer.pp_typ ty;
      all_elem [] @@ Integer.pred (direct_array_size ty)
    | _ -> [Set (lv, e, loc)]
  in

  let rec expand lv ty loc =
    match unrollType ty with
    | TComp (mcomp, _, _) ->
      let field fi =
        let newlv = addOffsetLval (Field (fi, NoOffset)) lv in
        expand newlv fi.ftype loc
      in
      List.(flatten @@ map field mcomp.cfields)
    | TArray _ ->
      let elem i =
        let cste = constant_expr i in
        let newlv = addOffsetLval (Index(cste,NoOffset)) lv in
        expand newlv (direct_element_type ty) loc
      in
      let rec all_elem acc i =
        if Integer.(ge i zero) then
          all_elem (elem i @ acc) (Integer.pred i)
        else acc
      in
      if is_reference_type ty then
        fatal "array expansion called on a reference type: %a: %a" Printer.pp_lval lv Printer.pp_typ ty;
      all_elem [] @@ Integer.pred (direct_array_size ty)
    | _ -> [lv]
  in

object(self)

  inherit frama_c_inplace

  method! vglob_aux =
    let retype_func fvi =
      let formal (n, ty, a) =
        let ty = if isStructOrUnionType ty then mkTRef ty "Norm.vglob_aux" else ty in
        n, ty, a
      in
      let rt, params, isva, a = splitFunctionTypeVI fvi in
      let params =
        match params with
        | None -> None
        | Some p -> Some (List.map formal p)
      in
      let rt = if isStructOrUnionType rt then mkTRef rt "Norm.vglob_aux(2)" else rt in
      fvi.vtype <- TFun (rt, params, isva, a)
    in
    function
    | GVarDecl(_spec,v,_attr) ->
      if isFunctionType v.vtype && not v.vdefined then retype_func v;
      DoChildren
    | GFun _
    | GAnnot _ -> DoChildren
    | GVar _  | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method! vfunc f =
    let var v =
      if isStructOrUnionType v.vtype then
        let newv = copyVarinfo v @@ unique_name ("v_" ^ v.vname) in
        newv.vtype <- mkTRef newv.vtype "Norm.vfunc";
        v.vformal <- false;
        let rhs =
          new_exp ~loc:v.vdecl @@
            Lval
              (mkMem
                 (new_exp ~loc:v.vdecl @@ Lval(Var newv,NoOffset)) NoOffset)
        in
        let copy = mkassign_statement (Var v, NoOffset) rhs v.vdecl in
        add_pending_statement ~beginning:true copy;
        pairs := (v, newv) :: !pairs;
        [v], newv
      else
        [], v
    in
    (* Insert copy statements. *)
    let locvl, formvl = List.(split @@ map var f.sformals) in
    (* Set locals and formals. *)
    let locvl = List.flatten locvl in
    f.slocals <- locvl @ f.slocals;
    setFormals f formvl;
    (* Add local variable for return *)
    let rt = getReturnType f.svar.vtype in
    if isStructOrUnionType rt then
      let rv = makeTempVar (the self#current_func) rt in
      return_var := Some rv;
      Htbl_vi.add return_vars rv ()
    else
      return_var := None;
    (* Change return type. *)
    new_return_type := if isStructOrUnionType rt then Some (mkTRef rt "Norm.vfunc(3)") else None;
    let rt = if isStructOrUnionType rt then mkTRef rt "Norm.vfunc(4)" else rt in
    setReturnType f rt;
    DoChildren

  method! vbehavior b =
    let lval loc lv = expand lv (typeOfLval lv) loc in
    let term t =
      match t.term_node with
      | TLval tlv ->
        let lv, env = force_term_lval_to_lval tlv in
        let lvlist = lval t.term_loc lv in
        let tslvlist = List.map (force_back_lval_to_term_lval env) lvlist in
        List.map
          (fun tslv ->
             Logic_const.term ~loc:t.term_loc (TLval tslv) t.term_type)
          tslvlist
      | Tempty_set -> [t]
        (* most of the case below are still to do *)
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
      | Tnull -> [t]
        (* those cases can not appear as assigns *)
      | TSizeOf _ | TSizeOfE _ | TSizeOfStr _ | TAlignOf _ | TAlignOfE _
      | Tlambda _ | TDataCons _ | Tbase_addr _ | TBinOp _ | TUnOp _
      | Tblock_length _ | TCoerce _ | TCoerceE _ | TUpdate _
      | Ttypeof _ | Ttype _ | Tlet _ | Toffset _ | Toffset_max _ | Toffset_min _ ->
        fatal "unexpected term in assigns clause: %a" Printer.pp_term t
    in
    let zone idts =
      List.map Logic_const.new_identified_term (term idts.it_content)
    in
    let assign (z, froms) =
      let zl = zone z in
      (* The \from clause isn't handled by Jessie translation anyway (there is no such clause in Jessie language) *)
      (* But the full expansion can cause the plugin to hang, so we don't expand \froms *)
      List.map (fun x -> x, froms) zl
    in
    let assigns = (* b.b_assigns *)
      (* the following may stop completely the execution of the plugin ??? *)
      (* Mikhail: Because \assigns as1 \from as2 if, for instance, as1 and as2 *)
      (*          are some arrays (about 50 elements) of big structures (about 50 fields),  *)
      (*          can expand to (50*50)^2=6250000 i.e. > 6 million term pairs.  *)
      (*          But isn't it the case that the \from clause in \assigns is ignored later anyway? *)
      (*          Then we can expand only the Writes part. *)
      match b.b_assigns with
      | WritesAny -> WritesAny
      | Writes l -> Writes List.(flatten @@ map assign l)
    in
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
    ChangeDoChildrenPost (new_bhv, id)

  method! vstmt_aux s =
    match s.skind with
    | Return (Some e, loc) when isStructOrUnionType (typeOf e) ->
      (* Type of [e] has not been changed by retyping formals and return. *)
(*           match e with *)
(*             | Lval lv -> *)
(*                 let skind = Return(Some(Cabs2cil.mkAddrOfAndMark lv),loc) in *)
(*                 ChangeTo { s with skind = skind; } *)
(*             | _ -> assert false (\* Should not be possible *\) *)
      let lv = Var (the !return_var), NoOffset in
      let ret = mkStmt @@ Return (Some (Cabs2cil.mkAddrOfAndMark loc lv), loc) in
      let assigns = expand_assign lv e (typeOf e) loc in
      let assigns = List.map (fun i -> mkStmt (Instr i)) assigns in
      let block = Block (mkBlock @@ assigns @ [ret]) in
      ChangeTo { s with skind = block }
    | Return (Some _, _) -> SkipChildren
    | _ -> DoChildren

  method! vinst =
    function
    | Set (lv, e, loc) when isStructOrUnionType (typeOf e) ->
      (* Type of [e] has not been changed by retyping formals and return. *)
      ChangeTo (expand_assign lv e (typeOf e) loc)
    | Set _ -> SkipChildren
    | Call (lvo, callee, args, loc) ->
      let args =
        List.map
          (fun arg ->
            (* Type of [arg] has not been changed. *)
            if isStructOrUnionType (typeOf arg) then
              match arg.enode with
              | Lval lv -> Cabs2cil.mkAddrOfAndMark loc lv
              | _ ->
                (* Should not be possible *)
                fatal
                  "vinst: direct struct or union passed as something different from lvalue: %a: %a"
                  Printer.pp_exp arg Printer.pp_typ (typeOf arg)
            else arg)
          args
      in
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
            makeTempVar (the self#current_func) (mkTRef lvty "Norm.vinst")
          in
          let tmplv = Var tmpv, NoOffset in
          let call = Call (Some tmplv, callee, args, loc) in
          let deref =
            new_exp ~loc @@
              Lval
                (mkMem
                  (new_exp ~loc @@ Lval (Var tmpv, NoOffset)) NoOffset)
          in
          let assign = mkassign lv deref loc in
          let free = mkfree tmpv loc in
          ChangeTo [call; assign; free]
        else
          let call = Call(lvo,callee,args,loc) in
          ChangeTo [call]
      end
    | Asm _ | Skip _ -> SkipChildren
    | Code_annot _ -> fatal "code annotation: shold have been removed in register.ml"

  method! vterm_lval tlv =
    ChangeDoChildrenPost (tlv, postaction_term_lval)

  method! vterm t =
    (* Renormalize the term tree. *)
    let postaction t =
      match t.term_node with
      | TAddrOf(TMem t,TNoOffset) -> t
      | _ -> t
    in
    ChangeDoChildrenPost (t, postaction)

end

let expand_struct_assign file =
  visitFramacFile (visit_and_push_statements_visitor (new struct_assign_expander ())) file


(*****************************************************************************)
(* Move first substructure fields out to the outer structures to simplify    *)
(* the successive subtyping relation computation.                            *)
(*****************************************************************************)

class embed_first_substructs_visitor =
  let subfield_name ci fi = unique_name @@ ci.cname ^ "_" ^ fi.fname in
  let is_embedded, embed_first_substruct, get_field  =
    let module FI = Cil_datatype.Fieldinfo in
    let module FH = FI.Hashtbl in
    let embedded_fields = FH.create 10 in
    let field_map = FH.create 10 in
    (fun efi -> try FH.find embedded_fields efi with Not_found -> false),
    (fun ci ci' ->
      let efi, cfields = List.(hd ci.cfields, tl ci.cfields) in
      let cfields' =
        List.map
          (fun fi ->
             let fi' =
               { fi with
                 fcomp = ci;
                 fname = subfield_name ci' fi;
                 fattr =
                   addAttribute (Attr (embedded_attr_name,
                                       [AStr efi.forig_name; AStr (compFullName ci'); AStr fi.forig_name])) fi.fattr }
             in
             let fs =
               try FH.find field_map efi
               with
               | Not_found ->
                 let fs = FH.create 10 in
                 FH.replace field_map efi fs;
                 fs
             in
             FH.replace fs fi fi';
             fi')
          ci'.cfields
      in
      ci.cfields <- cfields' @ cfields;
      FH.replace embedded_fields efi true),
    fun efi -> FH.(find (find field_map efi))
  in
  let do_offs =
    function
    | Field (fi, Field (fi', NoOffset)) as offs when is_embedded fi ->
      begin try
        Field (get_field fi fi', NoOffset)
      with
      | Not_found -> offs (* Possible when address of an embedded field is taken *)
      end
    | off -> off
  in
  let do_expr e =
    match e.enode with
    | AddrOf (host, off) ->
      let off =
        visitFramacOffset
          (object
            inherit frama_c_inplace
            method! voffs _ =
              DoChildrenPost
                (function
                 | Field (fi, offs) when is_embedded fi ->
                   offs
                 | off -> off)
          end)
          off
      in
      mkCast ~force:true ~e:(mkAddrOf ~loc:e.eloc (host, off)) ~newt:(typeOf e)
    | _ -> e
  in
object
  inherit frama_c_inplace

  method! vcompinfo ci =
    match ci.cfields with
    | { ftype; fattr } :: _ when isStructOrUnionType ftype && not (hasAttribute noembed_attr_name fattr) ->
      begin match unrollType ftype with
      | TComp (ci', _, _) when ci'.cstruct ->
        embed_first_substruct ci ci';
        SkipChildren
      | _ -> SkipChildren
      end
    | _ -> SkipChildren

  method! voffs _ = DoChildrenPost do_offs
  method! vterm_offset = do_on_term_offset (None, Some do_offs)

  method! vexpr _ = DoChildrenPost do_expr
  method! vterm = do_on_term (None, Some do_expr)

end

let embed_first_substructs = visitFramacFile (new embed_first_substructs_visitor)

(*****************************************************************************)
(* Rewrite type char* into void* in successive castings.                     *)
(*****************************************************************************)

class char_pointer_rewriter =
object
  inherit frama_c_inplace

  method! vexpr e =
    let void_ptr_with_attrs t = typeAddAttributes (typeAttrs t) voidPtrType in
    match e.enode with
    | CastE (tcharp, ein)
      when isCharPtrType tcharp ->
        ChangeTo ({ e with enode = CastE (void_ptr_with_attrs tcharp, ein)})
    | BinOp _ ->
      DoChildrenPost
        (function
         | { enode = BinOp (op, e1, e2, _); eloc } -> mkBinOp ~loc:eloc op e1 e2
         | e -> fatal "vexpr: unexpected transformation of BinOp to: %a" Printer.pp_exp e)
    | UnOp (op, ( { eloc } as e), typ) when isCharPtrType typ ->
        ChangeDoChildrenPost (new_exp ~loc:eloc (UnOp (op, e, void_ptr_with_attrs typ)), id)
    | _ -> DoChildren
end

class side_cast_rewriter =
  let has_charp_casts e =
    try
      ignore @@ visitFramacExpr
        (object
          inherit frama_c_inplace
          method! vexpr =
            function
            | { enode = CastE (tcharp, _) }
              when isCharPtrType tcharp -> raise Exit
            | _ -> DoChildren
         end)
        e;
      false
    with Exit -> true
  in
  let rewrite_char_pointers = visitFramacExpr (new char_pointer_rewriter) in
  let struct_fields t =
    match unrollType t with
    | TComp (compinfo, _, _) -> compinfo.cfields
    | t -> fatal "struct_fields: expected composite type, got: %a" Printer.pp_typ t
  in
  let pointed_type t =
    match unrollType t with
    | TPtr _ as t -> typeOf_pointed t
    | TArray _ as t -> typeOf_array_elem t
    | t -> t
  in
  let subtype t1 t2 =
    isVoidPtrType t2 ||
    let t1, t2 = map_pair pointed_type (t1, t2) in
    Cil_datatype.Typ.equal t1 t2 ||
    isStructOrUnionType t1 && isStructOrUnionType t2 &&
    let fields1, fields2 = map_pair struct_fields (t1, t2) in
    let len1, len2 = map_pair List.length (fields1, fields2) in
    len1 > len2 &&
    List.for_all2
      (fun fi1 fi2 -> Retype.same_fields fi1 fi2)
      (take len2 fields1)
      fields2
  in
object(self)
  inherit frama_c_inplace

  method! vexpr e =
    match e.enode with
    | CastE (tto, efrom)
      when isCharPtrType (typeOf efrom) &&
           isPointerType tto &&
           not (isCharPtrType tto) &&
           not (isVoidPtrType tto) &&
           has_charp_casts efrom ->
      ChangeTo ({ e with enode = CastE (tto, rewrite_char_pointers efrom) })
    | CastE (tto, efrom) ->
      let tfrom = typeOf efrom in
      if (isPointerType tfrom || isArrayType tfrom) &&
         (isPointerType tto || isArrayType tto) &&
         let tto = typeDeepDropAllAttributes tto
         and tfrom = typeDeepDropAllAttributes tfrom in
         not (subtype tto tfrom || subtype tfrom tto)
      then
        let void_ptr_type = typeAddAttributes (typeAttrs tfrom) voidConstPtrType in
        ChangeDoChildrenPost
          ({ e with enode = CastE (tto, mkCastT ~force:false ~e:efrom ~oldt:tfrom ~newt:void_ptr_type)}, id)
      else
        DoChildren
    | _ -> DoChildren

  method! vterm =
    do_on_term (Some (fun e -> match self#vexpr e with ChangeTo e | ChangeDoChildrenPost (e, _) -> e | _ -> e), None)
end

let rewrite_side_casts file =
  visitFramacFile (new side_cast_rewriter) file

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

class struct_variables_retyping_visitor =

  let varset = ref Set_vi.empty in
  let lvarset = ref Set_lv.empty in

  let postaction_lval (host, off) =
    let host =
      match host with
      | Var v when Set_vi.mem v !varset ->
        Mem (mkInfo @@
               new_exp ~loc:(Cil_const.CurrentLoc.get ()) @@
                  Lval (Var v, NoOffset))
      | Var _ | Mem _ -> host
    in
    host, off
  in
  let postaction_tlval (host, off) =
    let add_deref host v =
      TMem (mkterm (TLval (host, TNoOffset)) v.lv_type @@ Cil_const.CurrentLoc.get ())
    in
    let host =
      match host with
      | TVar v ->
        if Set_lv.mem v !lvarset then
          add_deref host v
        else
          may_map
           ~dft:host
           (fun cv ->
              if Set_vi.mem cv !varset then
                add_deref host v
              else host)
           v.lv_origin
      | TMem _ | TResult _ -> host
    in
    host, off
  in
object(self)

  inherit frama_c_inplace

  method! vvdec v =
    if isStructOrUnionType v.vtype && not v.vformal then  begin
      v.vtype <- mkTRef v.vtype "Norm.vvdec";
      varset := Set_vi.add v !varset
    end;
    DoChildren

  method! vquantifiers vl =
    List.iter
      (fun v ->
        (* Only iterate on logic variable with C type *)
        if app_term_type (fun _ -> true) false v.lv_type then
          match v.lv_origin with
          | None -> ()
          | Some v -> ignore (self#vvdec v))
      vl;
    DoChildren

  method! vlogic_var_decl v =
    let newty =
      app_term_type
        (fun ty -> Ctype (if isStructOrUnionType ty then mkTRef ty "Norm.vlogic_var_decl" else ty))
        v.lv_type v.lv_type
    in
    v.lv_type <- newty;
    DoChildren

  method! vglob_aux =
    function
    | GVar (_, _, _) as g ->
      let postaction =
        function
        | [GVar (v, _, _)] when Set_vi.mem v !varset ->
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
            Cil_const.make_logic_info @@ unique_logic_name ("valid_" ^ v.vname)
          in
          globinv.l_labels <- [label_here];
          globinv.l_body <- LBpred p;
          attach_globaction (fun () -> Logic_utils.add_logic_function globinv);
          [g; GAnnot (Dinvariant (globinv, v.vdecl), v.vdecl)]
        | [GVar _] -> [g]
        | _ -> fatal "transformed variable to somethig else during normalization: %a" Printer.pp_global g
      in
      ChangeDoChildrenPost ([g], postaction)
    | GVarDecl _ | GFun _ | GAnnot _ -> DoChildren
    | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method! vfunc f =
    (* First change type of local structure variables *)
    List.iter (ignore % visitCilVarDecl (self :> cilVisitor)) f.slocals;
    List.iter (ignore % visitCilVarDecl (self :> cilVisitor)) f.sformals;
    (* Then allocate/deallocate memory for those that need it *)
    List.iter
      (fun v ->
        if Set_vi.mem v !varset then
          let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
          add_pending_statement ~beginning:true ast;
          (* do not deallocate variable used in returning a structure *)
          if not (Htbl_vi.mem return_vars v) then
          let fst = mkfree_statement v v.vdecl in
          add_pending_statement ~beginning:false fst)
      f.slocals;
    DoChildren

  method! vlval lv = ChangeDoChildrenPost (lv, postaction_lval)

  method! vterm_lval lv = ChangeDoChildrenPost(lv, postaction_tlval)

  method! vexpr e =
    (* Renormalize the expression tree. *)
    let postaction e =
      match e.enode with
      | AddrOf (Mem e,NoOffset) -> e
      | _ -> e
    in
    ChangeDoChildrenPost (e, postaction)

  method! vterm t =
    (* Renormalize the term tree. *)
    let postaction t =
      match t.term_node with
      | TAddrOf(TMem t,TNoOffset) -> t
      | _ -> t
    in
    ChangeDoChildrenPost (t, postaction)

end

let retype_struct_variables file =
  visit_and_push_statements visit_and_update_globals (new struct_variables_retyping_visitor) file


(*****************************************************************************)
(* Retype variables and fields whose address is taken.                       *)
(*****************************************************************************)

module Set_fi = Cil_datatype.Fieldinfo.Set

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
class addrof_retyping_visitor =

  let varset = ref Set_vi.empty in
  let lvarset = ref Set_lv.empty in
  let fieldset = ref Set_fi.empty in

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
    if retypable_var v then begin
      v.vtype <- mkTRef v.vtype "Norm.retype_var";
      if not  (isPointerType v.vtype) then
        fatal "retypable var should be of pointer type (retype_var): %s" v.vname;
      varset := Set_vi.add v !varset
    end
  in
  let retype_lvar v =
    if retypable_lvar v then begin
      v.lv_type <- Ctype (force_app_term_type (fun x -> mkTRef x "Norm.retyp_lvar") v.lv_type);
      lvarset := Set_lv.add v !lvarset
    end
  in
  let retype_field fi =
    if retypable_field fi then begin
      fi.ftype <- mkTRef fi.ftype "Norm.retype_field";
      if not  (isPointerType fi.ftype) then
        fatal "retypable field should be of pointer type (retype_field): %s" fi.fname;
      fieldset := Set_fi.add fi !fieldset
    end
  in

  let postaction_lval (host,off) =
    let host =
      match host with
      | Var v when Set_vi.mem v !varset ->
        if not (isPointerType v.vtype) then
          fatal "retypable var should be of pointer type (postaction_lval): %s" v.vname;
        Mem (mkInfo @@
             new_exp ~loc:(Cil_const.CurrentLoc.get ()) @@ Lval (Var v, NoOffset))

      | Var _ | Mem _ -> host
    in
    (* Field retyped can only appear as the last offset, as it is of
     * base/pointer type.
     *)
    match lastOffset off with
    | Field (fi, _) when Set_fi.mem fi !fieldset ->
        if not  (isPointerType fi.ftype) then
          fatal "retypable field should be of pointer type (postaction_lval): %s" fi.fname;
        mkMem (mkInfo (new_exp ~loc:(Cil_const.CurrentLoc.get ()) @@ Lval (host, off))) NoOffset
    | _ -> host, off
  in

  let postaction_tlval (host, off) =
    let add_deref host ty =
      force_app_term_type ignore ty;
      TMem (mkterm (TLval (host, TNoOffset)) ty @@ Cil_const.CurrentLoc.get ())
    in
    let host =
      match host with
      | TVar v ->
        if Set_lv.mem v !lvarset then
          add_deref host v.lv_type
        else
          may_map
            ~dft:host
            (fun cv ->
               if Set_vi.mem cv !varset then
                 add_deref host (Ctype cv.vtype)
               else host)
            v.lv_origin
      | TResult _ | TMem _ -> host
    in
    match Logic_const.lastTermOffset off with
    | TField (fi, _) when Set_fi.mem fi !fieldset ->
      (TMem (Logic_const.term (TLval (host, off)) @@ Ctype fi.ftype), TNoOffset)
    | TField _ | TModel _ | TIndex _ | TNoOffset -> host, off
  in
  let postaction_expr e =
    match e.enode with
    | AddrOf (Var v, NoOffset) ->
      fatal  "address of a function: should have been eliminated before: %s" v.vname
      (* Host should have been turned into [Mem] *)
    | AddrOf (Mem e1, NoOffset) -> e1
    | AddrOf (_host, off) ->
      begin match lastOffset off with
      | Field (fi, _) when Set_fi.mem fi !fieldset ->
        fatal "postaction_expr: should have been turned into [Mem] with NoOffset: %a: %s" Printer.pp_exp e fi.fname
      | Index _ | Field _-> e
      | NoOffset ->
        (* Should be unreachable *)
        fatal "postaction_expr: NoOffset encountered where should be unreachable: %a" Printer.pp_exp e
      end
    | _ -> e
  in
  let postaction_term t =
    match t.term_node with
    | TAddrOf ((TVar _ | TResult _), TNoOffset) ->
      fatal "postaction_term: unexpected term: %a" Printer.pp_term t
    | TAddrOf (TMem t1, TNoOffset) -> t1
    | TAddrOf (_, off) ->
      begin match Logic_const.lastTermOffset off with
      | TField (fi, _) when Set_fi.mem fi !fieldset ->
        fatal "postaction_term: unexpected term offset: %a: %a" Printer.pp_term t Printer.pp_term_offset off
      | TField _ -> t
      | TModel _ -> unsupported "model field"
      | TIndex _ -> t
      | TNoOffset ->
        (* unreachable *)
        fatal "postaction_term: NoOffset encountered where should be unreachable: %a" Printer.pp_term t
      end
    | _ -> t
  in
  let varpairs : (varinfo * varinfo) list ref = ref [] in
  let in_funspec = ref false in
object

  inherit frama_c_inplace

  method! vglob_aux =
    function
    | GVar(v, _, _) ->
      if retypable_var v then
        retype_var v;
          (* Disabled, see BTS 0284
            let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
            attach_globinit ast
           *)
      SkipChildren
    | GVarDecl (_, v, _) ->
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
    | GAsm _ | GPragma _ | GText _ ->
      SkipChildren

  method! vfunc f =
    (* Change types before code. *)
    let formals, locals, pairs =
      List.fold_right
        (fun v (fl, ll, pl) ->
          if retypable_var v then
            let newv = copyVarinfo v ("v_" ^ v.vname) in
            newv.vaddrof <- false;
            v.vformal <- false;
            (newv :: fl, v :: ll, (v, newv) :: pl)
          else (v :: fl, ll, pl))
        f.sformals
        ([], [], [])
    in

    varpairs := pairs;
    setFormals f formals;
    f.slocals <- locals @ f.slocals;
    List.iter retype_var f.slocals;

    List.iter
      (fun v ->
        (* allocate/deallocate locals *)
        if Set_vi.mem v !varset then begin
          let ast = mkalloc_statement v (pointed_type v.vtype) v.vdecl in
          add_pending_statement ~beginning:true ast;
          (* do not deallocate variable used in returning a structure *)
          if not (Htbl_vi.mem return_vars v) then
            let fst = mkfree_statement v v.vdecl in
            add_pending_statement ~beginning:false fst
        end;
        (* allocate/deallocate formals *)
        try
          let loc = v.vdecl in
          (* [varpairs] holds pairs of (local,formal) to initialize due to
           * the transformation for formals whose address is taken.
           *)
          let fv = List.assoc v !varpairs in
          let lhs = mkMem (new_exp ~loc @@ Lval (Var v, NoOffset)) NoOffset in
          let rhs = new_exp ~loc @@ Lval (Var fv, NoOffset) in
          let assign = mkassign_statement lhs rhs loc in
          add_pending_statement ~beginning:true assign
        with
        | Not_found -> ())
      f.slocals;
    DoChildren

  method! vspec _ =
    in_funspec := true;
    DoChildrenPost (fun x -> in_funspec := false; x)

  method! vlogic_var_use v =
    if !in_funspec then
      match v.lv_origin with
      | None -> SkipChildren
      | Some cv ->
        try
          let fv = List.assoc cv !varpairs in
          ChangeTo (cvar_to_lvar fv)
        with
        | Not_found -> SkipChildren
    else begin
      if retypable_lvar v then retype_lvar v;
      DoChildren
   end

  method! vlogic_var_decl v = if retypable_lvar v then retype_lvar v; DoChildren

  method! vlval lv = ChangeDoChildrenPost (lv, postaction_lval)

  method! vterm_lval lv = ChangeDoChildrenPost (lv, postaction_tlval)

  method! vexpr e = ChangeDoChildrenPost (e, postaction_expr)

  method! vterm t = ChangeDoChildrenPost (t, postaction_term)

end

let retype_address_taken file =
  visit_and_push_statements visit_and_update_globals (new addrof_retyping_visitor) file


(*****************************************************************************)
(* Retype fields of type structure and array.                                *)
(*****************************************************************************)

module Htbl_fi =  Cil_datatype.Fieldinfo.Hashtbl

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
class fields_retyping_visitor =

  let field_to_array_type : typ Htbl_fi.t = Htbl_fi.create 0 in

  let postaction_lval (host, off) =
    let rec offset_list =
      function
      | NoOffset -> []
      | Field (fi, off) ->
        Field (fi, NoOffset) :: offset_list off
      | Index (e, Field (fi,off)) ->
        Index (e, Field (fi, NoOffset)) :: offset_list off
      | Index (_idx, NoOffset) as off -> [off]
      | Index (idx, (Index _ as off)) ->
        if !flatten_multi_dim_array then
          fatal
            "postaction_lval: the following index is incompatible with multi-dim array flattening: %a %a"
            Printer.pp_exp idx Printer.pp_offset off;
        Index (idx, NoOffset) :: offset_list off
    in
    let rec apply_lift_offset =
      function
      | Field (fi, roff) ->
        begin try
          let ty = Htbl_fi.find field_to_array_type fi in
          let roff = apply_lift_offset (lift_offset ty roff) in
          Field (fi, roff)
        with
        | Not_found ->
          let roff = apply_lift_offset roff in
          Field (fi, roff)
        end
      | Index (idx, roff) ->
        let roff = apply_lift_offset roff in
        Index (idx, roff)
      | NoOffset -> NoOffset
    in
    let off = if !flatten_multi_dim_array then apply_lift_offset off else off in
    (* [initlv] : topmost lval
     * [initlist] : list of offsets to apply to topmost lval
     *)
    let initlv, initlist =
      match offset_list off with
      | [] -> (host, NoOffset), []
      | fstoff :: roff -> (host, fstoff), roff
    in
    List.fold_left
      (fun curlv ->
         function
         | NoOffset ->
           (* should not occur *)
           fatal "lift_offset: unexpected NoOffset"
         | Field (_, _)
         | Index (_, Field (_ ,_))
         | Index(_, NoOffset) as nextoff ->
           Mem (mkInfo @@ new_exp ~loc:(Cil_const.CurrentLoc.get ()) @@ Lval curlv), nextoff
         | Index (_, Index _) ->
           fatal "lift_offset: unexpected index")
      initlv
      initlist
  in

  (* Renormalize the expression tree. *)
  let postaction_expr e =
    match e.enode with
    | AddrOf (Mem e, NoOffset) | StartOf (Mem e, NoOffset) -> e
    | AddrOf (Mem _e, Field (_fi, off) as lv)
    | StartOf (Mem _e, Field (_fi, off) as lv) ->
      if off <> NoOffset then fatal "postaction_expr: unexpected NoOffset: %a" Printer.pp_exp e;
      (* Only possibility is that field is of structure or union type,
       * otherwise [retype_address_taken] would have taken care of it.
       * Do not check it though, because type was modified in place.
       *)
      new_exp ~loc:e.eloc (Lval lv)
    | AddrOf (Mem e', Index (ie, NoOffset)) ->
      let ptrty = TPtr (typeOf e', []) in
      new_exp ~loc:e.eloc @@ BinOp (PlusPI, e', ie, ptrty)
    | StartOf (Mem _e, Index (_ie, NoOffset) as lv) ->
      new_exp ~loc:e.eloc (Lval lv)
    | AddrOf (Mem _e, Index (_ie, Field (_, NoOffset)) as lv)
    | StartOf (Mem _e, Index (_ie, Field (_, NoOffset)) as lv) ->
      new_exp ~loc:e.eloc (Lval lv)
    | AddrOf(Mem _e, Index(_ie, _)) | StartOf (Mem _e, Index(_ie, _)) ->
      fatal "unexpected index: %a" Printer.pp_exp e
    | _ -> e
  in
object

  inherit frama_c_inplace

  method! vglob_aux = function
    | GCompTag (compinfo,_) ->
      let field fi =
        if isStructOrUnionType fi.ftype then
          fi.ftype <- mkTRef fi.ftype "Norm.vglob_aux(2)"
        else if isArrayType fi.ftype then begin
          Htbl_fi.replace field_to_array_type fi fi.ftype;
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

  method! vlval lv = ChangeDoChildrenPost (lv, postaction_lval)

  method! vterm_lval = do_on_term_lval (None, Some postaction_lval)

  method! vexpr e =  ChangeDoChildrenPost(e, postaction_expr)

  method! vterm = do_on_term (None, Some postaction_expr)

end

let retype_fields file =
  visitFramacFile (new fields_retyping_visitor) file

(*****************************************************************************)
(* Retype pointers to base types.                                            *)
(*****************************************************************************)

module Htbl_ty = Cil_datatype.Typ.Hashtbl
module Set_ty = Cil_datatype.Typ.Set

(* Retype pointer to base type T to pointer to struct S with:
 * - if T is [TVoid], no field in S
 * - otherwise, a single field of type T in S
 *)
class base_retyping_visitor =

  (* Correspondance between a base type and its wrapper structure type *)
  let type_wrappers = Htbl_ty.create 17 in
  (* Store which types are wrapper types *)
  let auto_type_wrappers = ref Set_ty.empty in

  let is_wrapper_type ty = Set_ty.mem ty !auto_type_wrappers in

  let new_wrapper_for_type_no_sharing ty =
    (* Choose name t_P for the wrapper and t_M for the field *)
    let name = type_name ty in
    let wrapper_name = name ^ "P" in
    let field_name = name ^ "M" in
    let compinfo =
      if isVoidType ty then mkStructEmpty wrapper_name
      else mkStructSingleton wrapper_name field_name ty
    in
    let tdef = GCompTag (compinfo, Cil_datatype.Location.unknown) in
    let tdecl = TComp (compinfo,empty_size_cache () ,[]) in
    attach_global tdef;
    tdef, tdecl
  in
object(self)

  (* Helper methods called on the [self] object *)

  method new_wrapper_for_type ty =
    (* Currently, do not make any difference between a pointer to const T
     * or volatile T and a pointer to T.
     *)
    let ty = typeRemoveAttributes ["const"; "volatile"] (unrollType ty) in
    try
      Htbl_ty.find type_wrappers ty
    with
    | Not_found ->
      (* Construct a new wrapper for this type *)
      let wrapper_def,wrapper_type = new_wrapper_for_type_no_sharing ty in
      Htbl_ty.replace type_wrappers ty wrapper_type;
      auto_type_wrappers := Set_ty.add wrapper_type !auto_type_wrappers;
      (* Treat newly constructed type *)
      let store_current_global = !currentGlobal in
      ignore @@ visitCilGlobal (self :> cilVisitor) wrapper_def;
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
    | TPtr(_elemty, attr) ->
      (* Do not use [_elemty] directly but rather [pointed_type ty] in order
       * to get to the array element in references, i.e. pointers to arrays.
       *)
       let elemty = pointed_type ty in
       if is_wrapper_type elemty then
         Some ty
       else if isStructOrUnionType elemty then
         None (* Already in a suitable form for Jessie translation. *)
       else if is_array_reference_type ty then begin
        (* Do not lose the information that this type is a reference *)
        let size = constant_expr (Integer.of_int64 (reference_size ty)) in
        if !flatten_multi_dim_array && is_reference_type elemty then
          fatal "failed to flatten multi-dim array: %a" Printer.pp_typ ty;
        Some (mkTRefArray (self#new_wrapper_for_type elemty, size, []))
       end else if is_reference_type ty then
        (* Do not lose the information that this type is a reference *)
        Some (mkTRef (self#new_wrapper_for_type elemty) "Norm.private wrap_type_if_needed")
      else
        (* Here is the case where a transformation is needed *)
        Some (TPtr (self#new_wrapper_for_type elemty, attr))
    | TArray (_, len, size, attr) ->
      (*[VP-20100826] Can happen in case of logic term translation *)
      let elemty = element_type ty in
      if is_wrapper_type elemty then
        Some ty
      else if isStructOrUnionType elemty then
        None
      else
        Some (TArray (self#new_wrapper_for_type elemty, len, size ,attr))
    | TFun _ -> None
    | TNamed (typeinfo, _attr) ->
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
    | Mem e, (Index (ie, _) as off) when is_last_offset off ->
      begin match self#wrap_type_if_needed (typeOf e) with
      | Some newtyp ->
        let newfi = get_unique_field (pointed_type newtyp) in
        let newlv =
        if isArrayType (direct_pointed_type newtyp) then
          lv
        else (* The array has been directly decayed into a pointer
                Use pointer arithmetic instead of index. *)
          Mem (new_exp ~loc:e.eloc @@ BinOp (PlusPI, e, ie, newtyp)), NoOffset
        in
        let newlv = addOffsetLval (Field (newfi, NoOffset)) newlv in
        newlv
      | None -> lv
      end
    | Mem _, Index _
    | Mem _, Field _ -> lv

  (* Usual methods in visitor interface. *)

  inherit frama_c_inplace

  method! vfile _ =
    struct_type_for_void := self#new_wrapper_for_type voidType;
    DoChildren

  method! vtype ty =
    let ty =
      match self#wrap_type_if_needed ty with
      | Some newty -> newty
      | None -> ty
    in
    if isFunctionType ty then
      (* Applies changes in particular to parameter types in function types. *)
      ChangeDoChildrenPost (ty, id)
    else
      ChangeTo ty

  method! vglob_aux =
    let retype_return v =
      let retyp = getReturnType v.vtype in
      let newtyp = visitCilType (self :> cilVisitor) retyp in
      if newtyp != retyp then setReturnTypeVI v newtyp
    in
    function
    | GType (typeinfo, _) ->
      ignore @@ self#wrap_type_if_needed (TNamed (typeinfo, []));
      SkipChildren
    | GCompTag (compinfo, _) ->
      ignore @@ self#wrap_type_if_needed (TComp (compinfo, empty_size_cache (), []));
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

  method! vlval lv = ChangeDoChildrenPost (lv, self#postaction_lval)

  method! vterm_lval t = do_on_term_lval (None, Some self#postaction_lval) t

end

let retype_base_pointer file =
  visit_and_update_globals (new base_retyping_visitor :> frama_c_visitor) file


(*****************************************************************************)
(* Remove useless casts.                                                     *)
(*****************************************************************************)

class useless_casts_remover =
  let preaction_expr etop =
    match (stripInfo etop).enode with
    | CastE (ty, e) ->
      let ety = typeOf e in
      if isPointerType ty && isPointerType ety &&
         Cil_datatype.Typ.equal
           (typeDeepDropAttributes ["const"; "volatile"] @@ pointed_type ty)
           (typeDeepDropAttributes ["const"; "volatile"] @@ pointed_type ety)
      then e
      else etop
    | _ -> etop
  in
  let preaction_term term =
    match term.term_node with
    | TCastE (ty, t) when isPointerType ty && Logic_utils.isLogicPointer t ->
      (* Ignore type qualifiers *)
      let pty = Cil.typeDeepDropAllAttributes (pointed_type ty) in
      let ptty =
        match t.term_type with
        | Ctype tty ->
          if isPointerType tty then pointed_type tty
          else element_type tty
        | ty ->
          fatal "preaction_term: not a pointer type: %a" Printer.pp_logic_type ty
      in
      if Cil_datatype.Typ.equal pty ptty then
        if Logic_utils.isLogicPointerType t.term_type then
          t
        else begin
          match t.term_node with
          | TLval lv -> Logic_const.term (TStartOf lv) (Ctype ty)
          | TStartOf _ -> t
          | _ ->
            fatal
              "preaction_term: unexpected array expression casted into pointer: %a"
              Printer.pp_term t
        end
      else term
    | _ -> term
  in
object

  inherit frama_c_inplace

  method! vexpr e = ChangeDoChildrenPost (preaction_expr e, id)

  method! vterm t = ChangeDoChildrenPost (preaction_term t, id)

end

let remove_useless_casts file = visitFramacFile (new useless_casts_remover) file


(*****************************************************************************)
(* Translate union fields into structures                                    *)
(*****************************************************************************)

let generated_union_types = Htbl_ty.create 0

class unions_translator =
  let field_to_equiv_type : typ Htbl_fi.t = Htbl_fi.create 0 in
  let new_field_type fi =
    let tname = unique_name (fi.fname ^ "P") in
    let fname = unique_name (fi.fname ^ "M") in
    let padding = the fi.fpadding_in_bits in
    let mcomp = mkStructSingleton ~padding tname fname fi.ftype in
    let tdef = GCompTag (mcomp, CurrentLoc.get ()) in
    let tdecl = TComp (mcomp, empty_size_cache (), []) in
    Htbl_ty.add generated_union_types tdecl ();
    Htbl_fi.add field_to_equiv_type fi tdecl;
    fi.ftype <- tdecl;
    tdef
  in

  let postaction_offset = function
    | Field(fi,off) as off' ->
      begin try
        let ty = Htbl_fi.find field_to_equiv_type fi in
        let newfi = get_unique_field ty in
        Field (fi, Field (newfi, off))
      with
      | Not_found -> off'
      end
    | off -> off
  in
object

  inherit frama_c_inplace

  method! vglob_aux = function
  | GCompTag (compinfo,_) as g when not compinfo.cstruct ->
    let fields = compinfo.cfields in
    let field fi = new_field_type fi in
    let fty = List.map field fields in
    ChangeTo (g :: fty)
  | GFun _ | GAnnot _ | GVar _ | GVarDecl _ -> DoChildren
  | GCompTag _ | GType _ | GCompTagDecl _ | GEnumTagDecl _
  | GEnumTag _ | GAsm _ | GPragma _ | GText _ -> SkipChildren

  method! voffs off = ChangeDoChildrenPost (off, postaction_offset)

  method! vterm_offset = do_on_term_offset (None, Some postaction_offset)

end

let translate_unions file = visitFramacFile (new unions_translator) file

(*****************************************************************************)
(* Remove array address.                                                     *)
(*****************************************************************************)

class array_address_remover =
object

  inherit frama_c_inplace

  method! vexpr e =
    let preaction e =
      match e.enode with
      | AddrOf (Mem ptre, Index (ie, NoOffset)) ->
        let ptrty = typeOf e in
        new_exp ~loc:e.eloc @@ BinOp (PlusPI, ptre, ie, ptrty)
      | _ -> e
    in
    ChangeDoChildrenPost (preaction e, id)

  method! vterm t =
    let preaction t =
      match t.term_node with
      | TAddrOf(TMem ptrt,TIndex(it,TNoOffset)) ->
        { t with term_node = TBinOp (PlusPI, ptrt, it) }
      | _ -> t
    in
    ChangeDoChildrenPost (preaction t, id)

  (* TODO: translate to add tsets easily *)

end

let remove_array_address file = visitFramacFile (new array_address_remover) file


(*****************************************************************************)
(* Normalize the C file for Jessie translation.                              *)
(*****************************************************************************)

let normalize file =
  let apply = Rewrite.apply ~file in
  (* Retype variables of array type. *)
  (* order: before [expand_struct_assign] and any other pass which calls
     [typeOf], because "t[i]" with [StartOf] if type of "t" is "int t[a][b]"
     is not typed correctly by Cil (raises error StartOf on non-array type).
     See, e.g., example array_addr.c. *)
  apply retype_array_variables "retyping variables of array type";
  (* Retype logic functions/predicates with structure parameters or return. *)
  apply retype_logic_functions "retyping logic functions/predicates";
  (* Expand structure copying through parameter, return or assignment. *)
  (* order: before [retype_address_taken], before [retype_struct_variables] *)
  apply expand_struct_assign "expanding structure copying";
  (* Embed fields of first fist substructures *)
  apply embed_first_substructs "embedding fields of first substructures";
  (* Rewrite char * into void * in successive casts. *)
  apply rewrite_side_casts "rewriting type char* into void* in successive casts";
  (* Retype variables of structure type. *)
  apply retype_struct_variables "retyping variables of structure type";
  (* Retype variables and fields whose address is taken. *)
  (* order: after [retype_struct_variables] *)
  apply retype_address_taken "retyping variables and fields whose address is taken";
  (* Expand structure copying through assignment. *)
  (* Needed because sequence [expand_struct_assign; retype_struct_variables;
     retype_address_taken] may recreate structure assignments. *)
  (* order: after [retype_address_taken] *)
  apply expand_struct_assign "expanding structure copying through assignment";
  (* Translate union fields into structures. *)
  apply translate_unions  "translate union fields into structures";
  (* Retype fields of type structure and array. *)
  (* order: after [expand_struct_assign] and [retype_address_taken]
   * before [translate_unions] *)
  apply retype_fields "retype fields of type structure and array";
  (* Retype fields of type structure and array. *)
  (* order: after [translate_unions] *)
  apply retype_fields "retyping fields of type structure and array";
  (* Remove array address. *)
  (* order: before [retype_base_pointer] *)
  apply remove_array_address "removing array address";
  (* Retype pointers to base types. *)
  (* order: after [retype_fields] *)
  apply retype_base_pointer "retyping pointers to base types";
  (* Remove useless casts. *)
  apply remove_useless_casts "removng useless casts"

(*
Local Variables:
compile-command: "make -C .."
End:
*)
