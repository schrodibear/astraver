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

open Jc
open Stdlib
open Common
open Env
open Struct_tools
open Region
open Interp_misc
open Output_ast
open Output_misc

module Output = (val Options.backend)

(* Helper functions *)

(* Returns all alloc classes for the struct and all its nested embeded fields *)

let select_all ~on_bv f ac pc =
  match ac with
  | JCalloc_bitvector -> on_bv
  | JCalloc_root rt ->
    match rt.ri_kind with
    | Rvariant
    | RdiscrUnion -> f ?select:(Some fully_allocated) pc
    | RplainUnion -> on_bv

let all_allocs_ac ac = select_all ~on_bv:[ac] all_allocs ac

let all_mems_ac = select_all ~on_bv:[] all_memories

let all_tags_ac = select_all ~on_bv:[] all_tags

let deref_if_needed ~in_param lab (is_not_cte, v) =
  match v with
  | LDeref _ when is_not_cte -> v
  | LDeref x -> LVar x
  | LVar x when in_param -> lvar ~constant:false ~label_in_name:false lab x
  | LVar _ -> v
  | t -> failwith @@ Format.asprintf "deref_if_needed got unexpected expression: %a" Output.fprintf_term t

type ('a, 'b, 'c) where =
  | In_app : ('b, 'b, 'c) where
  | In_pred : ('c, 'b, 'c) where

let mems ac pc (type t) : (t, region -> term list, (string * logic_type) list) where -> t =
  let map f = List.map f (all_mems_ac ac pc) in
  function
  | In_app -> fun r -> map @@ fun mc -> tmemory_var ~label_in_name:false LabelHere (mc, r)
  | In_pred -> map (fdup2 Name.Generic.memory memory_type)

let allocs ac pc (type t) : (t, region -> in_param:bool -> label -> term list, (string * logic_type) list) where -> t =
  let map f = List.map f (all_allocs_ac ac pc) in
  function
  | In_app ->
    fun r ~in_param lab ->
    map @@ fun ac -> deref_if_needed ~in_param lab @@ talloc_table_var ~label_in_name:false LabelHere (ac, r)
  | In_pred -> map (fdup2 Name.Generic.alloc_table alloc_table_type)

let tags ac pc (type t) : (t, region -> in_param:bool -> label -> term list, (string * logic_type) list) where -> t =
  let map f = List.map f (all_tags_ac ac pc) in
  function
  | In_app ->
    fun r ~in_param lab ->
    map @@ fun ac -> deref_if_needed ~in_param lab @@ ttag_table_var ~label_in_name:false LabelHere (ac, r)
  | In_pred -> map @@ fdup2 (Name.tag_table % fun ac -> ac, dummy_region) tag_table_type

let map_st ~f ac pc =
  match ac with
  | JCalloc_bitvector -> []
  | JCalloc_root rt ->
    match rt.ri_kind with
    | Rvariant ->
      begin match pc with
      | JCtag (st, _) ->
        f st
      | JCroot _ -> []
      end
    | RdiscrUnion
    | RplainUnion -> []

let map_embedded_fields ~f ~p ac =
  map_st ac
    ~f:(fun st ->
          ListLabels.map
            st.si_fields
            ~f:(function
                | { fi_type = JCTpointer (fpc, Some fa, Some fb) } as fi ->
                  f ~acr:(alloc_class_of_pointer_class fpc, dummy_region) ~pc:fpc ~p:(make_select_fi fi p) ~l:fa ~r:fb
                | _ -> []))

(* Validity *)

let valid ~in_param ~equal (ac, r) pc p ao bo =
  let params =
    allocs ac pc In_app r ~in_param LabelHere @ mems ac pc In_app r |>
    Option.fold_right ~f:List.cons bo |>
    Option.fold_right ~f:List.cons ao
  in
  LPred (Name.Pred.valid ~equal ~left:(ao <> None) ~right:(bo <> None) ac pc, p :: params)

(* If T is a structure:
     valid_T(p, a, b, allocs ...) =
       if T is root:
         offset_min(alloc_i, p) == a &&
         offset_max(alloc_i, p) == b
       else if S is the direct superclass of T:
         valid_S(p, a, b, allocs ...)
       and for all field (T'[a'..b'] f) of p,
         valid_T'(p.f, a', b', allocs ...)
  If T is a variant, then we only have the condition on offset_min and max. *)
let valid_pred ~in_param ~equal ?(left=true) ?(right=true) ac pc =
  let p = "p" in
  let a = "a" in
  let b = "b" in
  let params =
    let p = p, pointer_type ac pc in
    let a = a, why_integer_type in
    let b = b, why_integer_type in
    p :: (
      allocs ac pc In_pred @ mems ac pc In_pred |>
      Fn.on right (List.cons b) |>
      Fn.on left (List.cons a))
  in
  let validity =
    let omin, omax, super_valid =
      match pc with
      | JCtag ({ si_parent = Some(st, pp) }, _) ->
        let super_valid =
          valid ~in_param ~equal
            (ac, dummy_region) (JCtag (st, pp)) (LVar p)
            (if left then Some (LVar a) else None)
            (if right then Some (LVar b) else None)
        in
        LTrue, LTrue, super_valid
      | JCtag ({ si_parent = None }, _)
      | JCroot _ ->
        (if equal then make_eq else make_le) (make_offset_min ac (LVar p)) (LVar a),
        (if equal then make_eq else make_ge) (make_offset_max ac (LVar p)) (LVar b),
        LTrue
    in
    let fields_valid =
      List.flatten @@
        map_embedded_fields ac pc ~p:(LVar p)
          ~f:(fun ~acr ~pc ~p ~l ~r ->
            [valid ~in_param ~equal:false acr pc p
               (if left then Some (const_of_num l) else None)
               (if right then Some (const_of_num r) else None)])
    in
    let validity = super_valid :: fields_valid in
    let validity = if right then omax :: validity else validity in
    let validity = if left then omin :: validity else validity in
    make_and_list validity
  in
  Predicate (false, id_no_loc (Name.Pred.valid ~equal ~left ~right ac pc), params, validity)

(* Freshness *)

let fresh ~for_ ~in_param (ac, r) pc p =
  let params =
    (match for_ with `alloc_tables -> allocs | `tag_tables -> tags) ac pc In_app r ~in_param LabelOld
    @ mems ac pc In_app r
  in
  LPred (Name.Pred.fresh ~for_ ac pc, p :: params)

let fresh_pred ~for_ ac pc =
  let p = "p" in
  let params =
    let p = p, pointer_type ac pc in
    let tables =
      match for_ with
      | `alloc_tables -> allocs
      | `tag_tables -> tags
    in
    p :: tables ac pc In_pred @ mems ac pc In_pred
  in
  let super_fresh =
    match pc with
    | JCtag ({ si_parent = Some (st, pp) }, _) ->
      [fresh ~for_ ~in_param:false (ac, dummy_region) (JCtag (st, pp)) (LVar p)]
    | JCtag ({ si_parent = None }, _)
    | JCroot _ ->
      map_st ac pc
        ~f:(fun st ->
            let predicate, table =
              match for_ with
              | `alloc_tables -> "alloc_fresh", Name.Generic.alloc_table ac
              | `tag_tables -> "tag_fresh", Name.Generic.tag_table (struct_root st)
            in
            [LPred (predicate, [LVar table; LVar p])])
  in
  let fields_fresh p =
    List.flatten @@
      map_embedded_fields ac pc ~p
        ~f:(fun ~acr ~pc ~p ~l:_ ~r:_ -> [fresh ~for_ ~in_param:false acr pc p])
  in
  let freshness = make_and_list @@ super_fresh @ fields_fresh (LVar p) in
  Predicate (false, id_no_loc (Name.Pred.fresh ~for_ ac pc), params, freshness)

(* Instanceof *)

let forall_offset_in_range p l r ~f =
  if f (LConst Prim_void) <> [] then
    let i = "i" in
      LForall (i, why_integer_type, [],
        LImpl (make_and (LPred ("le_int", [l; LVar i])) @@ LPred ("lt_int", [LVar i; r]),
               make_and_list @@ f @@ LApp ("shift", [p; LVar i])))
  else LTrue

type (_, 'a) param =
  | Void : ([`Singleton], 'a) param
  | N : 'a -> ([`Range_0_n], 'a) param
  | L_R : 'a * 'a -> ([`Range_l_r], 'a) param

let get_n = function N n -> n

let get_l = function L_R (l, _) -> l

let get_r = function L_R (_, r) -> r

let instanceof ~exact (type t1) (type t2) :
  arg:(assertion, _, term -> term -> assertion, _, t1, t2) arg -> in_param:_ -> _ -> _ -> _ -> t2 =
  fun ~arg ~in_param (ac, r) pc p ->
  let params = tags ac pc In_app r ~in_param LabelHere @ mems ac pc In_app r in
  match arg with
  | Singleton -> LPred (Name.Pred.instanceof ~exact ~arg ac pc, p :: params)
  | Range_l_r -> fun l r -> LPred (Name.Pred.instanceof ~exact ~arg ac pc, p :: l :: r :: params)

let instanceof_pred ~exact
    (type t1) (type t2) : arg : (assertion, _, term -> term -> assertion, _, t1, t2) arg -> _ =
  fun ~arg ac pc ->
  let p = "p" in
  let l_r : (t1, _) param =
    match arg with
    | Singleton -> Void
    | Range_l_r -> L_R ("l", "r")
  in
  let params =
    let p = p, pointer_type ac pc in
    let l_r =
      match arg with
      | Singleton -> []
      | Range_l_r -> List.map (fun a -> a, why_integer_type) [get_l l_r; get_r l_r]
    in
    p :: l_r @ tags ac pc In_pred @ mems ac pc In_pred
  in
  let pred_name = if exact then "eq" else "subtag" in
  let self_instanceof p =
    map_st ac pc
      ~f:(fun st ->
          let tag = Name.Generic.tag_table (struct_root st) in
          [LPred (pred_name, [make_typeof (LVar tag) p; LVar (Name.tag st)])])
  in
  let fields_instanceof p =
    List.flatten @@
      map_embedded_fields ac pc ~p
        ~f:(fun ~acr ~pc ~p ~l ~r ->
              let open Num in
              if r -/ l >=/ Int 0 && l -/ r <=/ Int Options.forall_inst_bound then
                let instanceof p =
                  instanceof ~exact ~arg:Singleton ~in_param:false acr pc p
                in
                instanceof p ::
                  (List.(range ~-1 `Downto (int_of_num l) @ range 1 `To (int_of_num r)) |>
                   List.map @@ fun i -> instanceof @@ LApp ("shift", [p; const_of_int i]))
              else
                let r = r +/ Int 1 in
                let l, r = Pair.map const_of_num (l, r) in
                [instanceof ~exact ~arg:Range_l_r ~in_param:false acr pc p l r])
  in
  match arg with
  | Singleton ->
    let instanceof = make_and_list @@ self_instanceof (LVar p) @ fields_instanceof (LVar p) in
    Predicate (false, id_no_loc (Name.Pred.instanceof ~exact ~arg ac pc), params, instanceof)
  | Range_l_r ->
    let instanceof =
      let instanceof p = self_instanceof p @ fields_instanceof p in
      make_and_list @@
        instanceof (LVar p) @
        [forall_offset_in_range (LVar p) (LVar (get_l l_r)) (LVar (get_r l_r))
          ~f:(fun p -> instanceof p)]
    in
    Predicate (false, id_no_loc (Name.Pred.instanceof ~exact ~arg ac pc), params, instanceof)

(* Alloc *)

let frame ~for_ ~in_param (ac, r) pc p n =
  let params =
    let tables =
      let map ~f l = List.(flatten @@ map f l) in
      let tables_for ~tx_table_var ~name_of_x xc =
        if in_param then
          let xt = tx_table_var ~label_in_name:false LabelHere (xc, r) in
          let deref = deref_if_needed ~in_param:true in
          [deref LabelOld xt; deref LabelHere xt]
        else
          let xt = name_of_x xc in
          [LVar (Name.old xt); LVar xt]
      in
      match for_ with
      | `alloc_tables ->
        map (all_allocs_ac ac pc)
          ~f:(tables_for ~tx_table_var:talloc_table_var ~name_of_x:Name.Generic.alloc_table)
      | `tag_tables ->
        map (all_tags_ac ac pc)
          ~f:(tables_for ~tx_table_var:ttag_table_var ~name_of_x:Name.Generic.tag_table)
    in
    tables @ mems ac pc In_app r
  in
  LPred (Name.Pred.frame ~for_ ac pc, p :: n :: params)

let frame_pred ~for_ ac pc =
  let p = "p" in
  let n = "n" in
  let params =
    let tables =
      let map  ~f l = List.(flatten @@ map f l) in
      let tables_for ~name_of_x ~x_table_type =
          (fun name_type -> [map_fst Name.old name_type; name_type])
        % fdup2 name_of_x x_table_type
      in
      match for_ with
      | `alloc_tables ->
        map (all_allocs_ac ac pc)
          ~f:(tables_for ~name_of_x:Name.Generic.alloc_table ~x_table_type:alloc_table_type)
      | `tag_tables ->
        map (all_tags_ac ac pc)
          ~f:(tables_for ~name_of_x:Name.Generic.tag_table ~x_table_type:tag_table_type)
    in
    [p, pointer_type ac pc; n, why_integer_type] @ tables @ mems ac pc In_pred
  in
  let frame =
    let assc =
      let p = LVar p in
      let n = LVar n in
      let name_of_x ac =
        match for_ with
        | `alloc_tables -> Name.Generic.alloc_table ac
        | `tag_tables ->
          match ac with
          | JCalloc_bitvector ->
            Options.jc_error Why_loc.dummy_position "Unsupported alloc_struct frame conditions for bitvector regions"
          | JCalloc_root ri ->
            Name.Generic.tag_table ri
      in
      let assoc ac p = name_of_x ac, p, None in
      let rec frame ac pc p =
        assoc ac p ::
        (List.flatten @@
          map_embedded_fields ac pc ~p
            ~f:(fun ~acr:(ac, _) ~pc ~p ~l ~r ->
                if Num.(l <=/ r) then frame ac pc p else []))
      in
      frame ac pc p |>
      fun l -> List.(let xt, p, _ = hd l in (xt, p, Some n) :: tl l)
    in
    let cmp (a1, _, _) (a2, _, _) = compare a1 a2 in
    List.(group_consecutive (fun x -> cmp x %> (=) 0) @@ sort cmp assc) |>
    (let make_predicates pred xt args =
      let tables = [LVar (Name.old xt); LVar xt] in
      [LPred ((match for_ with `alloc_tables -> "alloc"  | `tag_tables -> "tag") ^ "_extends", tables);
       LPred (pred, tables @ args)]
     in
     List.map
       (function
         | [xt, p, Some n] ->
           let f = match for_ with `alloc_tables -> "alloc_block" | `tag_tables -> "alloc_tag_block" in
           make_predicates f xt [p; n]
         | (xt, p, _) :: ps ->
           let f = "alloc" ^ (match for_ with `alloc_tables -> "" | `tag_tables -> "_tag") ^ "_blockset" in
           make_predicates f xt
             [let pset_singleton p = LApp ("pset_singleton", [p]) in
              List.fold_left
                (fun acc (_, p, _) -> LApp ("pset_union", [acc; pset_singleton p]))
                (pset_singleton p)
                ps]
        | _ -> assert false (* group_consecutive doesn't return [[]], it instead returns just [] *)))
    |>
    List.flatten |>
    make_and_list
  in
  Predicate (false, id_no_loc (Name.Pred.frame ~for_ ac pc), params, frame)

(* Allocation *)

let alloc_write_parameters (ac, r) pc =
  let allocs = List.map (fdup2 (fun ac -> plain_alloc_table_var (ac, r)) alloc_table_type) @@ all_allocs_ac ac pc in
  let tags = List.map (fdup2 (fun vi -> plain_tag_table_var (vi, r)) tag_table_type) @@ all_tags_ac ac pc in
  allocs @ tags

let alloc_read_parameters (ac, r) pc =
  let mems =
    List.map (fdup2 (fun mc -> memory_var ~test_current_function:true (mc, r)) memory_type) @@
      all_mems_ac ac pc
  in
  mems

let alloc (type t1) (type t2) :
  arg:((expr, check_size:bool -> expr -> expr, _, _, t1, t2) arg) -> _ -> _ -> t2 =
  fun ~arg (ac, r) pc ->
    let args =
      let writes = alloc_write_parameters (ac, r) pc in
      let reads = alloc_read_parameters (ac, r) pc in
      List.map fst (writes @ reads)
    in
    match arg with
    | Singleton ->
      make_app (Name.Param.alloc ~arg:Singleton ac pc) args
    | Range_0_n ->
      fun ~check_size e ->
        make_app
          (Name.Param.alloc ~arg:Range_0_n ~check_size ac pc)
          (e :: args)

let alloc_param (type t1) (type t2) :
  arg:(why_decl, check_size:bool -> why_decl, _, _, t1, t2) arg -> _ -> _ -> t2 =
  fun ~arg ac pc ->
  let error = failwith % Format.asprintf "unexpected parameter expression in make_alloc_param: %a" Output.fprintf_expr in
  let n : (t1, _) param =
    match arg with
    | Singleton -> Void
    | Range_0_n -> N "n"
  in
  (* parameters and effects *)
  let writes = alloc_write_parameters (ac, dummy_region) pc in
  let write_effects = List.map (function ({ expr_node = Var n }, _ty') -> n | (e, _) -> error e) writes in
  let params =
    let write_params = List.map (fun (n, ty') -> (n, Ref_type (Base_type ty'))) writes in
    let reads = alloc_read_parameters (ac, dummy_region) pc in
    let read_params = List.map (fun (n, ty') -> (n, Base_type ty')) reads in
    (match arg with
     | Singleton -> []
     | Range_0_n -> [(mk_var (get_n n), Base_type why_integer_type)])
    @ write_params @ read_params
    |>
    List.map (function ({expr_node = Var n}, ty') -> (n, ty') | (e, _) -> error e)
  in
  let lresult = LVar "result" in
  (* postcondition *)
  let instanceof_post =
    let f ~arg = instanceof ~exact:true ~arg ~in_param:true (ac, dummy_region) pc lresult in
    let f =
      match arg with
      | Singleton -> fun _ -> [f ~arg:Singleton]
      | Range_0_n -> fun _ -> [f ~arg:Range_l_r (const_of_int 0) @@ LVar (get_n n)]
    in
    map_st ~f ac pc
  in
  let alloc_type pre =
    List.fold_right (fun (n, ty') acc -> Prod_type (n, ty', acc)) params @@
    Annot_type
     ((* [n >= 0] *)
      pre,
      (* argument pointer type *)
      Base_type (pointer_type ac pc),
      (* reads and writes *)
      [], write_effects,
      (* normal post *)
      make_and_list (
        (* [valid_st(result, 0, n-1, alloc ...)] *)
        let rbound, size =
          match arg with
          | Singleton -> Pair.map const_of_int (0, 1)
          | Range_0_n -> LApp ("sub_int", [LVar (get_n n); const_of_int 1]), LVar (get_n n)
        in
        [valid ~in_param:true ~equal:true (ac, dummy_region) pc lresult
           (Some (const_of_int 0)) (Some rbound);
         frame ~for_:`alloc_tables ~in_param:true (ac, dummy_region) pc lresult size;
         frame ~for_:`tag_tables ~in_param:true (ac, dummy_region) pc lresult size;
         fresh ~for_:`alloc_tables ~in_param:true (ac, dummy_region) pc lresult;
         fresh ~for_:`tag_tables ~in_param:true (ac, dummy_region) pc lresult]
        @ instanceof_post),
      (* no exceptional post *)
      [])
  in
  let name = Name.Param.alloc ac pc in
  match arg with
  | Singleton -> Param (false, id_no_loc @@ name ~arg:Singleton, alloc_type LTrue)
  | Range_0_n ->
    fun ~check_size ->
    (* precondition *)
    let pre =
      if check_size then LPred ("ge_int", [LVar (get_n n); const_of_int 0])
                    else LTrue
    in
    Param (false, id_no_loc @@ name ~arg:Range_0_n ~check_size, alloc_type pre)

let struc si =
  let tag_id_type =
    List.cons
      (let tagid_type = tag_id_type (struct_root si) in
       Logic (false, id_no_loc (Name.tag si), [], tagid_type))
  in
  let alloc_free_preds_and_params =
    Fn.on'
      (not @@ struct_of_union si)
      (fun () ->
         List.append @@
         let pc = JCtag (si, []) in
         let ac = alloc_class_of_pointer_class pc in
         let in_param = false in

         valid_pred ~in_param ~equal:true ac pc ::
         valid_pred ~in_param ~equal:false ac pc ::
         valid_pred ~in_param ~equal:false ~right:false ac pc ::
         valid_pred ~in_param ~equal:false ~left:false ac pc ::

         instanceof_pred ~exact:false ~arg:Range_l_r ac pc ::
         instanceof_pred ~exact:false ~arg:Singleton ac pc ::
         instanceof_pred ~exact:true ~arg:Range_l_r ac pc ::
         instanceof_pred ~exact:true ~arg:Singleton ac pc ::

         fresh_pred ~for_:`alloc_tables ac pc ::
         fresh_pred ~for_:`tag_tables ac pc ::

         frame_pred ~for_:`alloc_tables ac pc ::
         frame_pred ~for_:`tag_tables ac pc ::

         alloc_param ~arg:Singleton ac pc ::
         alloc_param ~arg:Range_0_n ~check_size:true ac pc ::
         alloc_param ~arg:Range_0_n ~check_size:false ac pc :: [])
  in
  let instanceof_implies_typeof_if_final =
    Fn.on'
      si.si_final
      (fun () ->
         List.append @@
         [Goal (KAxiom, id_no_loc (si.si_name ^ "_is_final"),
                let ri = Option.value_fail ~in_:"Interp_struct.struc" si.si_hroot.si_root in
                let t = "t" and p = "p" in
                let lt = LVar t and lp = LVar p in
                LForall (t, tag_table_type ri, [],
                         LForall (p, pointer_type (JCalloc_root ri) (JCtag (si, [])), [],
                                  LImpl (make_instanceof lt lp si,
                                         make_typeeq lt lp si))))])
  in
  let parent_tag_axiom =
    List.cons
      begin match si.si_parent with
      | None ->
        let name = si.si_name ^ "_parenttag_bottom" in
        let p = LPred ("parenttag", [LVar (Name.tag si); LVar "bottom_tag" ]) in
        Goal (KAxiom, id_no_loc name, p)
      | Some (p, _) ->
        let name = si.si_name ^ "_parenttag_" ^ p.si_name in
        let p = LPred ("parenttag", [LVar (Name.tag si); LVar (Name.tag p)]) in
        Goal (KAxiom, id_no_loc name, p)
      end
  in
  tag_id_type %>
  alloc_free_preds_and_params %>
  instanceof_implies_typeof_if_final %>
  parent_tag_axiom

let root =
  let fresh_tag_id =
    let counter = ref 0 in
    fun () -> incr counter; !counter
  in
  fun ri ->
    let tag_id_type =
      List.cons @@ Type (id_no_loc (Name.Type.root ri), [])
    in
    let preds_and_params =
      let ac = JCalloc_root ri and pc = JCroot ri in
      let in_param = false in
      List.append @@
      if root_is_union ri then
        valid_pred ~in_param ~equal:true ac pc ::
        valid_pred ~in_param ~equal:false ac pc ::
        valid_pred ~in_param ~equal:false ~right:false ac pc ::
        valid_pred ~in_param ~equal:false ~left:false ac pc ::

        alloc_param ~arg:Singleton ac pc ::
        alloc_param ~arg:Range_0_n ~check_size:true ac pc ::
        alloc_param ~arg:Range_0_n ~check_size:false ac pc :: []
      else
        valid_pred ~in_param:false ~equal:true ac pc ::
        valid_pred ~in_param:false ~equal:false ac pc :: []
    in
    let int_of_tag_axioms =
      List.append @@
      ListLabels.fold_left
        ri.ri_hroots
        ~init:[]
        ~f:(fun acc st ->
          Goal (KAxiom,
                id_no_loc (Name.Axiom.int_of_tag st),
                make_eq
                  (make_int_of_tag st)
                  (LConst (Prim_int (string_of_int @@ fresh_tag_id ()))))
          :: acc)
    in
    let same_typeof_in_block_if_struct =
      Fn.on'
        (not @@ root_is_union ri)
        (fun () ->
           List.cons @@
           Goal (KAxiom, id_no_loc (ri.ri_name ^ "_whole_block_tag"),
                 let t = "t" and p = "p" and q = "q" in
                 let lt = LVar t and lp = LVar p and lq = LVar q in
                 let ri_pointer_type = pointer_type (JCalloc_root ri) (JCroot ri) in
                 LForall (t, tag_table_type ri, [],
                          LForall (p, ri_pointer_type, [],
                                   LForall (q, ri_pointer_type, [],
                                            LImpl (LPred ("same_block", [lp; lq]),
                                                   LPred ("eq", [make_typeof lt lp; make_typeof lt lq])))))))
    in
    tag_id_type %>
    preds_and_params %>
    int_of_tag_axioms %>
    same_typeof_in_block_if_struct

let valid_pre ~in_param all_effects (* vi *) =
  function
  | { vi_type = JCTpointer (pc, lo, ro); vi_region } as vi
    when AllocMap.mem (alloc_class_of_pointer_class pc, vi.vi_region) all_effects.Fenv.e_alloc_tables ->
    (* TODO: what about bitwise? *)
    let v = tvar ~label_in_name:false LabelHere vi in
    begin match lo, ro with
    | None, None -> LTrue
    | Some n, None ->
      let ac = alloc_class_of_pointer_class pc in
      valid ~in_param ~equal:false (ac, vi_region) pc v (Some (const_of_num n)) None
    | None, Some n ->
      let ac = alloc_class_of_pointer_class pc in
      valid ~in_param ~equal:false (ac, vi_region) pc v None (Some (const_of_num n))
    | Some n1, Some n2 ->
      let ac = alloc_class_of_pointer_class pc in
      valid  ~in_param ~equal:false (ac, vi_region) pc v (Some (const_of_num n1)) (Some (const_of_num n2))
    end
  |  _ -> LTrue

let instanceof_pre ~in_param all_effects (* vi *) =
  function
  | { vi_type = JCTpointer (pc, lo, ro) as vi_type; vi_region } as vi
    when
      AllocMap.mem (alloc_class_of_pointer_class pc, vi.vi_region) all_effects.Fenv.e_alloc_tables &&
      TagMap.mem (pointer_class_root pc, vi_region) all_effects.Fenv.e_tag_tables ->
    let ac = alloc_class_of_pointer_class pc in
    let si = pointer_struct vi_type in
    let v = tvar ~label_in_name:false LabelHere vi in
    let pre, (l, r) =
      let _, at = talloc_table_var ~label_in_name:false LabelHere (ac, vi_region) in
      LPred ("allocated", [at; v]),
      Pair.map
        ((lo, "offset_min"), (ro, "offset_max"))
        ~f:(function Some n, _ -> const_of_num n | None, f -> LApp (f, [at; v]))
    in
    LImpl (pre, instanceof ~exact:si.si_final ~in_param (ac, vi_region) pc v ~arg:Range_l_r l r)
  | _ -> LTrue
