(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
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
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Stdlib
open Common
open Env
open Struct_tools
open Region
open Interp_misc
open Output_ast

module O = Output

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
  O.T.some @@
  match (v : _ term) with
  | Deref _ when is_not_cte -> v
  | Deref x -> O.T.(var x)
  | Var x when in_param -> lvar ~constant:false ~label_in_name:false lab x
  | Var _ -> v
  | _ -> failwith "deref_if_needed got unexpected expression"

type ('a, 'b, 'c) where =
  | In_app : ('b, 'b, 'c) where
  | In_pred : ('c, 'b, 'c) where

let mems : type t. _ -> _ -> (t, region -> some_term list, (string * some_logic_type) list) where -> t = fun ac pc ->
  let map f = List.map f (all_mems_ac ac pc) in
  function
  | In_app -> fun r -> map @@ fun mc -> O.T.some @@ tmemory_var ~label_in_name:false LabelHere (mc, r)
  | In_pred -> map (fdup2 Name.Generic.memory (O.Lt.some % memory_type))

let allocs :
  type t.
  _ -> _ -> (t, region -> in_param:bool -> label -> some_term list, (string * some_logic_type) list) where -> t =
  fun ac pc ->
  let map f = List.map f (all_allocs_ac ac pc) in
  function
  | In_app ->
    fun r ~in_param lab ->
    map @@ fun ac -> deref_if_needed ~in_param lab @@ talloc_table_var ~label_in_name:false LabelHere (ac, r)
  | In_pred -> map (fdup2 Name.Generic.alloc_table (O.Lt.some % alloc_table_type))

let tags :
  type t.
  _ -> _ -> (t, region -> in_param:bool -> label -> some_term list, (string * some_logic_type) list) where -> t =
  fun ac pc ->
  let map f = List.map f (all_tags_ac ac pc) in
  function
  | In_app ->
    fun r ~in_param lab ->
    map @@ fun ac -> deref_if_needed ~in_param lab @@ ttag_table_var ~label_in_name:false LabelHere (ac, r)
  | In_pred -> map @@ fdup2 (Name.tag_table % Pair.cons' dummy_region) (O.Lt.some % tag_table_type)

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
            f ~acr:(alloc_class_of_pointer_class fpc, dummy_region) ~pc:fpc ~p:O.T.(p **> fi) ~l:fa ~r:fb
          | _ -> []))

(* Validity *)

let valid ~in_param ~equal (ac, r) pc p ao bo =
  let params =
    allocs ac pc In_app r ~in_param LabelHere @ mems ac pc In_app r |>
    Option.fold_right' ~f:(List.cons % O.T.some) bo |>
    Option.fold_right' ~f:(List.cons % O.T.some) ao
  in
  O.P.(Name.Pred.valid ~equal ~left:P.(ao <> None) ~right:P.(bo <> None) ac pc $.. p ^.. params)

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
    let p = p, O.Lt.some (pointer_type ac pc) in
    let a = a, O.Lt.(some integer) in
    let b = b, O.Lt.(some integer) in
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
          let open O.T in
          valid ~in_param ~equal
            (ac, dummy_region) (JCtag (st, pp)) (var p)
            (if left then Some (var a) else None)
            (if right then Some (var b) else None)
        in
        True, True, super_valid
      | JCtag ({ si_parent = None }, _)
      | JCroot _ ->
        let open O.T in
        (if equal then (=) else (<=)) (offset_min ac (var p)) (var a),
        (if equal then (=) else (>=)) (offset_max ac (var p)) (var b),
        True
    in
    let fields_valid =
      List.flatten @@
        map_embedded_fields ac pc ~p:O.T.(var p)
          ~f:(fun ~acr ~pc ~p ~l ~r ->
            [valid ~in_param ~equal:false acr pc p
               (if left then Some O.T.(num l) else None)
               (if right then Some O.T.(num r) else None)])
    in
    let validity = super_valid :: fields_valid in
    let validity = if right then omax :: validity else validity in
    let validity = if left then omin :: validity else validity in
    O.P.conj validity
  in
  O.Wd.mk ~name:(snd @@ Name.Pred.valid ~equal ~left ~right ac pc) @@ Predicate (params, validity)

(* Freshness *)

let fresh ~for_ ~in_param (ac, r) pc p =
  let params =
    let lab =
      match for_ with
      | `alloc_tables_in `alloc | `tag_tables -> LabelOld
      | `alloc_tables_in `free -> LabelHere
    in
    (match for_ with `alloc_tables_in _ -> allocs | `tag_tables -> tags) ac pc In_app r ~in_param lab
    @ mems ac pc In_app r
  in
  let drop_in =
    function
    | `alloc_tables_in _ -> `alloc_tables
    | `tag_tables -> `tag_tables
  in
  O.P.(Name.Pred.fresh ~for_:(drop_in for_) ac pc $.. p ^.. params)

let fresh_pred ~for_ ac pc =
  let p = "p" in
  let params =
    let p = p, O.Lt.some (pointer_type ac pc) in
    let tables =
      match for_ with
      | `alloc_tables -> allocs
      | `tag_tables -> tags
    in
    p :: tables ac pc In_pred @ mems ac pc In_pred
  in
  let for_' =
    match for_ with
    | `alloc_tables -> `alloc_tables_in `alloc
    | `tag_tables -> `tag_tables
  in
  let super_fresh =
    match pc with
    | JCtag ({ si_parent = Some (st, pp) }, _) ->
      [fresh ~for_:for_' ~in_param:false (ac, dummy_region) (JCtag (st, pp)) O.T.(var p)]
    | JCtag ({ si_parent = None }, _)
    | JCroot _ ->
      map_st ac pc
        ~f:(fun si ->
            let predicate =
              match for_ with
              | `alloc_tables -> O.P.alloc_fresh ac
              | `tag_tables -> O.P.tag_fresh (struct_root si)
            in
            [predicate O.T.(var p)])
  in
  let fields_fresh p =
    List.flatten @@
      map_embedded_fields ac pc ~p
        ~f:(fun ~acr ~pc ~p ~l:_ ~r:_ -> [fresh ~for_:for_' ~in_param:false acr pc p])
  in
  let freshness = O.P.conj @@ super_fresh @ fields_fresh O.P.(T.var p) in
  O.Wd.mk ~name:(snd @@ Name.Pred.fresh ~for_ ac pc) @@ Predicate (params, freshness)

(* Instanceof *)

let forall_offset_in_range p l r ~f =
  if f (Const Void : _ term) <> [] then
    O.P.(
      forall "i" O.Lt.integer @@
      fun i ->
      impl
        (l <= i && i < r)
        (conj (f T.(shift p i))))
  else True

type (_, 'a) param =
  | Void : ([`Singleton], 'a) param
  | N : 'a -> ([`Range_0_n], 'a) param
  | L_R : 'a * 'a -> ([`Range_l_r], 'a) param

let get_n = function N n -> n

let get_l = function L_R (l, _) -> l

let get_r = function L_R (_, r) -> r

let instanceof ~exact (type t1) (type t2) :
  arg:(pred, _, unbounded integer number term -> unbounded integer number term -> pred, _, t1, t2) arg ->
  in_param:_ -> _ -> _ -> _ -> t2 =
  fun ~arg ~in_param (ac, r) pc p ->
  let params = tags ac pc In_app r ~in_param LabelHere @ mems ac pc In_app r in
  match arg with
  | Singleton -> O.P.(Name.Pred.instanceof ~exact ~arg ac pc $.. p ^.. params)
  | Range_l_r -> fun l r ->
    O.P.(Name.Pred.instanceof ~exact ~arg ac pc $.. p ^.. l ^.. r ^.. params)

let instanceof_pred ~exact (type t1) (type t2) :
  arg : (pred, _, unbounded integer number term -> unbounded integer number term -> pred, _, t1, t2) arg -> _ =
  fun ~arg ac pc ->
  let p = "p" in
  let l_r : (t1, _) param =
    match arg with
    | Singleton -> Void
    | Range_l_r -> L_R ("l", "r")
  in
  let params =
    let p = p, O.Lt.some (pointer_type ac pc) in
    let l_r =
      match arg with
      | Singleton -> []
      | Range_l_r -> List.map (fun a -> a, O.Lt.(some integer)) [get_l l_r; get_r l_r]
    in
    p :: l_r @ tags ac pc In_pred @ mems ac pc In_pred
  in
  let pred = O.P.(if exact then typeeq else instanceof) in
  let self_instanceof p = map_st ac pc ~f:(fun si -> O.P.[pred (struct_root si) p si]) in
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
                   List.map @@ fun i -> instanceof @@ O.T.(shift p @@ int i))
              else
                let r = r +/ Int 1 in
                let l, r = Pair.map O.T.num (l, r) in
                [instanceof ~exact ~arg:Range_l_r ~in_param:false acr pc p l r])
  in
  match arg with
  | Singleton ->
    let instanceof = O.P.conj @@ self_instanceof O.T.(var p) @ fields_instanceof O.T.(var p) in
    O.Wd.mk ~name:(snd @@ Name.Pred.instanceof ~exact ~arg ac pc) @@ Predicate (params, instanceof)
  | Range_l_r ->
    let instanceof =
      let instanceof' p = self_instanceof p @ fields_instanceof p in
      O.P.(
        conj @@
        instanceof' O.T.(var p) @
        [forall_offset_in_range O.T.(var p) O.T.(var (get_l l_r)) O.T.(var (get_r l_r))
          ~f:(fun p -> instanceof' p)])
    in
    O.Wd.mk ~name:(snd @@ Name.Pred.instanceof ~exact ~arg ac pc) @@ Predicate (params, instanceof)

(* Alloc *)

let frame ~for_ ~in_param (ac, r) pc p =
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
          O.T.[some @@ var (Name.old xt); some @@ var xt]
      in
      match for_ with
      | `alloc_tables_in _ ->
        map (all_allocs_ac ac pc)
          ~f:(tables_for ~tx_table_var:talloc_table_var ~name_of_x:Name.Generic.alloc_table)
      | `tag_tables ->
        map (all_tags_ac ac pc)
          ~f:(tables_for ~tx_table_var:ttag_table_var ~name_of_x:Name.Generic.tag_table)
    in
    (match for_ with `alloc_tables_in (`alloc n) -> [n] | _ -> []) @
    tables @ mems ac pc In_app r
  in
  let for_ =
    match for_ with
    | `alloc_tables_in (`alloc _) -> `alloc_tables_in `alloc
    | `alloc_tables_in `free | `tag_tables as f -> f
  in
  O.P.(Name.Pred.frame ~for_ ac pc $.. p ^.. params)

let frame_pred ~for_ ac pc =
  let p = "p" in
  let n = "n" in
  let params =
    let tables =
      let map  ~f l = List.(flatten @@ map f l) in
      let tables_for ~name_of_x ~x_table_type =
          (fun name_type -> [map_fst Name.old name_type; name_type])
        % fdup2 name_of_x (O.Lt.some % x_table_type)
      in
      match for_ with
      | `alloc_tables_in _ ->
        map (all_allocs_ac ac pc)
          ~f:(tables_for ~name_of_x:Name.Generic.alloc_table ~x_table_type:alloc_table_type)
      | `tag_tables ->
        map (all_tags_ac ac pc)
          ~f:(tables_for ~name_of_x:Name.Generic.tag_table ~x_table_type:tag_table_type)
    in
    let n = match for_ with `alloc_tables_in `alloc -> [n, O.Lt.(some integer)] | _ -> [] in
    (p, O.Lt.some @@ pointer_type ac pc) :: n @ tables @ mems ac pc In_pred
  in
  let frame =
    let assc =
      let p = O.T.var p in
      let n = O.T.var n in
      let name_of_x ac =
        match for_ with
        | `alloc_tables_in _ -> Name.Generic.alloc_table ac
        | `tag_tables ->
          match ac with
          | JCalloc_bitvector ->
            Options.jc_error Why_loc.dummy_position "Unsupported alloc_struct frame conditions for bitvector regions"
          | JCalloc_root ri ->
            Name.Generic.tag_table ri
      in
      let assoc ac p = name_of_x ac, O.T.some p, None in
      let rec frame ac pc p =
        assoc ac p ::
        (List.flatten @@
          map_embedded_fields ac pc ~p
            ~f:(fun ~acr:(ac, _) ~pc ~p ~l ~r ->
                if Num.(l <=/ r) then frame ac pc p else []))
      in
      frame ac pc p |>
      fun l -> List.(let xt, p, _ = hd l in (xt, p, Some (O.T.some n)) :: tl l)
    in
    let cmp (a1, _, _) (a2, _, _) = compare a1 a2 in
    List.(group_consecutive ~p:(fun x -> cmp x %> (=) 0) @@ sort cmp assc) |>
    (let prefix =
      function
      | `alloc -> "alloc"
      | `free -> "free"
     in
     let make_predicates pred xt args =
       let tables = O.T.[some @@ var (Name.old xt); some @@ var xt] in
       O.P.[
         P.(Name.Theory.jessie, (match for_ with `alloc_tables_in x -> prefix x | `tag_tables -> "tag") ^ "_extends")
         $.. tables;
         (Name.Theory.jessie, pred) $.. tables @ args]
     in
     List.map
       (function
         | [xt, p, Some n] ->
           let f, n =
             match for_ with
             | `alloc_tables_in x -> (prefix x) ^ "_block", if x = `alloc then [n] else []
             | `tag_tables -> "alloc_tag_block", []
           in
           make_predicates f xt (p :: n)
         | (xt, p, _) :: ps ->
           let f = "alloc" ^ (match for_ with `alloc_tables_in _ -> "" | `tag_tables -> "_tag") ^ "_blockset" in
           make_predicates f xt
             [let pset_singleton p = O.T.(some ((Name.Theory.jessie, "pset_singleton") $.. [p])) in
              List.fold_left
                (fun acc (_, p, _) -> O.T.(some ((Name.Theory.jessie, "pset_union") $.. [acc; pset_singleton p])))
                (pset_singleton p)
                ps]
        | _ -> assert false (* group_consecutive doesn't return [[]], it instead returns just [] *)))
    |>
    List.flatten |>
    O.P.conj
  in
  O.Wd.mk ~name:(snd @@ Name.Pred.frame ~for_ ac pc) @@ Predicate (params, frame)

(* Allocation *)

let alloc_write_parameters (ac, r) pc =
  let allocs =
    List.map
      (fdup2 (O.E.some % plain_alloc_table_var % Pair.cons' r) (O.Lt.some % alloc_table_type))
      (all_allocs_ac ac pc)
  in
  let tags =
    List.map
      (fdup2 (O.E.some % plain_tag_table_var % Pair.cons' r) (O.Lt.some % tag_table_type))
      (all_tags_ac ac pc)
  in
  allocs @ tags

let alloc_read_parameters (ac, r) pc =
  let mems =
    List.map (fdup2 (O.E.some % memory_var ~test_current_function:true % Pair.cons' r) (O.Lt.some % memory_type)) @@
      all_mems_ac ac pc
  in
  mems

let alloc : type t1 t2 a.
  arg:((a expr, check_size:bool -> unbounded integer number expr -> a expr, _, _, t1, t2) arg) -> _ -> _ -> t2 =
  fun ~arg (ac, r) pc ->
    let args =
      let writes = alloc_write_parameters (ac, r) pc in
      let reads = alloc_read_parameters (ac, r) pc in
      List.map fst (writes @ reads)
    in
    match arg with
    | Singleton ->
      O.E.(Name.Param.alloc ~arg:Singleton ac pc $.. args)
    | Range_0_n ->
      fun ~check_size e ->
        O.E.(Name.Param.alloc ~arg:Range_0_n ~check_size ac pc $.. e ^.. args)

let alloc_param : type t1 t2.
  arg:([`Module of bool] why_decl, check_size:bool -> [`Module of bool] why_decl, _, _, t1, t2) arg -> _ -> _ -> t2 =
  fun ~arg ac pc ->
  let error () = failwith "unexpected parameter expression in alloc_param" in
  let n : (t1, _) param =
    match arg with
    | Singleton -> Void
    | Range_0_n -> N "n"
  in
  (* parameters and effects *)
  let writes = alloc_write_parameters (ac, dummy_region) pc in
  let write_effects = List.map (function (Expr { expr_node = Var n }, _ty') -> n |  _ -> error ()) writes in
  let params =
    let write_params = List.map (fun (n, Logic_type ty') -> (n, Why_type (Ref_type (Base_type ty')))) writes in
    let reads = alloc_read_parameters (ac, dummy_region) pc in
    let read_params = List.map (fun (n, Logic_type ty') -> (n, Why_type (Base_type ty'))) reads in
    (match arg with
     | Singleton -> []
     | Range_0_n -> [O.E.(some @@ var (get_n n)), O.Wt.(some integer)])
    @ write_params @ read_params
    |>
    List.map (function (Expr { expr_node = Var n }, ty') -> (n, ty') |  _ -> error ())
  in
  let lresult = O.T.var "result" in
  (* postcondition *)
  let instanceof_post =
    let f ~arg = instanceof ~exact:true ~arg ~in_param:true (ac, dummy_region) pc lresult in
    let f =
      match arg with
      | Singleton -> fun _ -> [f ~arg:Singleton]
      | Range_0_n -> fun _ -> [f ~arg:Range_l_r (O.T.int 0) @@ O.T.var (get_n n)]
    in
    map_st ~f ac pc
  in
  let alloc_type pre =
    List.fold_right (fun (n, Why_type ty') (Why_type acc) -> Why_type (Prod_type (n, ty', acc))) params @@
    O.Wt.some @@
    Annot_type
     ((* [n >= 0] *)
      pre,
      (* argument pointer type *)
      Base_type (pointer_type ac pc),
      (* reads and writes *)
      [], write_effects,
      (* normal post *)
      O.P.conj (
        (* [valid_st(result, 0, n-1, alloc ...)] *)
        let rbound, size =
          map_snd O.T.some @@
          match arg with
          | Singleton -> Pair.map O.T.int (0, 1)
          | Range_0_n -> O.T.(var (get_n n) - int 1, var (get_n n))
        in
        [valid ~in_param:true ~equal:true (ac, dummy_region) pc lresult
           (Some (O.T.int 0)) (Some rbound);
         frame ~for_:(`alloc_tables_in (`alloc size)) ~in_param:true (ac, dummy_region) pc lresult;
         frame ~for_:`tag_tables ~in_param:true (ac, dummy_region) pc lresult;
         fresh ~for_:(`alloc_tables_in `alloc) ~in_param:true (ac, dummy_region) pc lresult;
         fresh ~for_:`tag_tables ~in_param:true (ac, dummy_region) pc lresult]
        @ instanceof_post),
      (* no exceptional post *)
      [])
  in
  let name = Name.Param.alloc ac pc in
  match arg with
  | Singleton ->
    let Why_type alloc_type = alloc_type True in
    O.Wd.mk ~name:(snd @@ name ~arg:Singleton) @@ Param alloc_type
  | Range_0_n ->
    fun ~check_size ->
      (* precondition *)
      let Why_type alloc_type =
        alloc_type @@
        if check_size then O.T.(var (get_n n) >= int 0)
                      else True
      in
      O.Wd.mk ~name:(snd @@ name ~arg:Range_0_n ~check_size) @@ Param alloc_type

(* Deallocation *)

let free_write_parameters (ac, r) pc =
  List.map
    (fdup2 (O.E.some % plain_alloc_table_var % Pair.cons' r) (O.Lt.some % alloc_table_type))
    (all_allocs_ac ac pc)

let free_read_parameters (ac, r) pc =
  List.map
    (fdup2 (O.E.some % memory_var ~test_current_function:true % Pair.cons' r) (O.Lt.some % memory_type))
    (all_mems_ac ac pc)

let free ~safe (ac, r) pc p =
  let args =
    let writes = free_write_parameters (ac, r) pc in
    let reads = free_read_parameters (ac, r) pc in
    p :: List.map fst (writes @ reads)
  in
  O.E.(Name.Param.free ~safe ac pc $.. args)

let free_param ~safe ac pc =
  let error () = failwith "unexpected parameter expression in free_param: %a" in
  (* parameters and effects *)
  let writes = free_write_parameters (ac, dummy_region) pc in
  let write_effects = List.map (function (Expr { expr_node = Var n }, _ty') -> n | _ -> error ()) writes in
  let p = "p" in
  let params =
    let write_params = List.map (fun (n, Logic_type ty') -> n, O.Wt.some @@ Ref_type (Base_type ty')) writes in
    let reads = free_read_parameters (ac, dummy_region) pc in
    let read_params = List.map (fun (n, Logic_type ty') -> (n, O.Wt.some @@ Base_type ty')) reads in
    write_params @ read_params |>
    List.map (function (Expr { expr_node = Var n }, ty') -> (n, ty') |  _ -> error ()) |>
    List.cons (p, O.Wt.some @@ Base_type (pointer_type ac pc))
  in
  let p = O.T.var p in
  let p_is_null = O.T.(p = var "null") in
  (* postcondition *)
  let Why_type free_type =
    List.fold_right (fun (n, Why_type ty') (Why_type acc) -> O.Wt.some @@ Prod_type (n, ty', acc)) params @@
    O.Wt.some @@
    let open O.P in
    Annot_type (
      (if P.not safe then
         (* allowed, see man 3 free *)
         positioned Position.dummy ~kind:(JCVCpre "Deallocation") @@
         p_is_null ||
         freeable ac ~r:dummy_region p
       else True),
      (* argument pointer type *)
      O.Wt.void,
      (* reads and writes *)
      [], write_effects,
      (* normal post *)
      (* null *)
      p_is_null &&
      conj (List.map (fun a -> T.(!. a = at a "")) write_effects) ||
      (* non-null *)
      frame ~for_:(`alloc_tables_in `free) ~in_param:true (ac, dummy_region) pc p &&
      fresh ~for_:(`alloc_tables_in `free) ~in_param:true (ac, dummy_region) pc p,
      (* no exceptional post *)
      [])
  in
  O.Wd.mk ~name:(snd @@ Name.Param.free ~safe ac pc) @@ Param free_type

let struc si =
  let tag_id_type =
      let tagid_type = tag_id_type (struct_root si) in
      O.Wd.mk ~name:(Name.tag si) @@ Logic ([], tagid_type)
  in
  let preds, safe_params, unsafe_params =
      if not @@ struct_of_union si then
        let pc = JCtag (si, []) in
        let ac = alloc_class_of_pointer_class pc in
        let in_param = false in

        [valid_pred ~in_param ~equal:true ac pc;
         valid_pred ~in_param ~equal:false ac pc;
         valid_pred ~in_param ~equal:false ~right:false ac pc;
         valid_pred ~in_param ~equal:false ~left:false ac pc;

         instanceof_pred ~exact:false ~arg:Range_l_r ac pc;
         instanceof_pred ~exact:false ~arg:Singleton ac pc;
         instanceof_pred ~exact:true ~arg:Range_l_r ac pc;
         instanceof_pred ~exact:true ~arg:Singleton ac pc;

         fresh_pred ~for_:`alloc_tables ac pc;
         fresh_pred ~for_:`tag_tables ac pc;

         frame_pred ~for_:(`alloc_tables_in `alloc) ac pc;
         frame_pred ~for_:(`alloc_tables_in `free) ac pc;
         frame_pred ~for_:`tag_tables ac pc],
        [alloc_param ~arg:Singleton ac pc;
         alloc_param ~arg:Range_0_n ~check_size:false ac pc;
         free_param ~safe:true ac pc],
        [alloc_param ~arg:Range_0_n ~check_size:true ac pc;
         free_param ~safe:false ac pc]
      else
        [], [], []
  in
  let instanceof_implies_typeof_if_final =
    if si.si_final then
      [O.Wd.mk ~name:(si.si_name ^ "_is_final") @@
       Goal (KAxiom,
             let ri = Option.value_fail ~in_:__LOC__ si.si_hroot.si_root in
             O.P.(forall (Name.Generic.tag_table (struct_root si)) (tag_table_type ri) @@ fun _t ->
                  forall "p" (pointer_type (JCalloc_root ri) (JCtag (si, []))) @@ fun p ->
                  impl
                    (instanceof (struct_root si)  p si)
                    (typeeq (struct_root si) p si)))]
    else
      []
  in
  let parent_tag_axiom =
    begin match si.si_parent with
    | None ->
      let p = O.(P.parenttag T.(var @@ Name.tag si) T.(var "bottom_tag")) in
      O.Wd.mk ~name:(si.si_name ^ "_parenttag_bottom") @@ Goal (KAxiom, p)
    | Some (parent, _) ->
      let p = O.(P.parenttag T.(var @@ Name.tag si) T.(var @@ Name.tag parent)) in
      O.Wd.mk ~name:(si.si_name ^ "_parenttag_" ^ parent.si_name) @@ Goal (KAxiom, p)
    end
  in
  O.[Entry.some @@
     Th.mk ~name:(fst @@ Name.Theory.struct_ (JCtag (si, []))) @@
     tag_id_type :: preds @ instanceof_implies_typeof_if_final @ parent_tag_axiom :: [];
     Entry.some @@
     Mod.mk ~name:(fst @@ Name.Module.struct_ ~safe:true (JCtag (si, []))) ~safe:true safe_params;
     Entry.some @@
     Mod.mk ~name:(fst @@ Name.Module.struct_ ~safe:false (JCtag (si, []))) ~safe:false unsafe_params]

let root =
  let fresh_tag_id =
    let counter = ref 0 in
    fun () -> incr counter; !counter
  in
  fun ri ->
    let tag_id_type =
      O.Wd.mk ~name:(Name.Type.root ri) @@ Type []
    in
    let preds, safe_params, unsafe_params =
      let ac = JCalloc_root ri and pc = JCroot ri in
      let in_param = false in
      if root_is_union ri then
        [valid_pred ~in_param ~equal:true ac pc;
         valid_pred ~in_param ~equal:false ac pc;
         valid_pred ~in_param ~equal:false ~right:false ac pc;
         valid_pred ~in_param ~equal:false ~left:false ac pc],
        [alloc_param ~arg:Singleton ac pc;
         alloc_param ~arg:Range_0_n ~check_size:false ac pc;
         free_param ~safe:true ac pc],
        [alloc_param ~arg:Range_0_n ~check_size:true ac pc;
         free_param ~safe:false ac pc]
      else if ri.ri_hroots = [] then
        [valid_pred ~in_param:false ~equal:true ac pc;
         valid_pred ~in_param:false ~equal:false ac pc],
        [],
        []
      else
        [], [], []
    in
    let int_of_tag_axioms =
      ListLabels.fold_left
        ri.ri_hroots
        ~init:[]
        ~f:(fun acc st ->
          (O.Wd.mk
             ~name:(Name.Axiom.int_of_tag st) @@
           Goal (KAxiom,
                 O.T.(int_of_tag (var (Name.tag st)) = int (fresh_tag_id ()))))
           :: acc)
    in
    let same_typeof_in_block_if_struct =
      if not (root_is_union ri) then
        [O.Wd.mk ~name:(ri.ri_name ^ "_whole_block_tag") @@
          Goal (KAxiom,
                 let ri_pointer_type = pointer_type (JCalloc_root ri) (JCroot ri) in
                 O.P.(
                   forall (Name.Generic.tag_table ri) (tag_table_type ri) @@ fun _ ->
                   forall "p" ri_pointer_type @@ fun p ->
                   forall "q" ri_pointer_type @@ fun q ->
                   impl (same_block p q)
                     T.(typeof ri p = typeof ri q)))]
      else
        []
    in
    O.[Entry.some @@
     Th.mk ~name:(fst @@ Name.Theory.struct_ (JCroot ri)) @@
     tag_id_type :: preds @ int_of_tag_axioms @ same_typeof_in_block_if_struct;
     Entry.some @@
     Mod.mk ~name:(fst @@ Name.Module.struct_ ~safe:true (JCroot ri)) ~safe:true safe_params;
     Entry.some @@
     Mod.mk ~name:(fst @@ Name.Module.struct_ ~safe:false (JCroot ri)) ~safe:false unsafe_params]

let valid_pre ~in_param all_effects (* vi *) =
  function
  | { vi_type = JCTpointer (pc, lo, ro); vi_region } as vi
    when AllocMap.mem (alloc_class_of_pointer_class pc, vi.vi_region) all_effects.Fenv.e_alloc_tables ->
    (* TODO: what about bitwise? *)
    let v = tvar ~label_in_name:false LabelHere vi in
    begin match lo, ro with
    | None, None -> True
    | Some n, None ->
      let ac = alloc_class_of_pointer_class pc in
      valid ~in_param ~equal:false (ac, vi_region) pc v (Some (O.T.num n)) None
    | None, Some n ->
      let ac = alloc_class_of_pointer_class pc in
      valid ~in_param ~equal:false (ac, vi_region) pc v None (Some (O.T.num n))
    | Some n1, Some n2 ->
      let ac = alloc_class_of_pointer_class pc in
      valid ~in_param ~equal:false (ac, vi_region) pc v (Some (O.T.num n1)) (Some (O.T.num n2))
    end
  |  _ -> True

let instanceof_pre all_effects (* vi *) =
  function
  | { vi_type = JCTpointer (pc, lo, ro) as vi_type; vi_region } as vi
    when
      AllocMap.mem (alloc_class_of_pointer_class pc, vi.vi_region) all_effects.Fenv.e_alloc_tables &&
      TagMap.mem (pointer_class_root pc, vi_region) all_effects.Fenv.e_tag_tables ->
    let ac = alloc_class_of_pointer_class pc in
    let si = pointer_struct vi_type in
    let v = tvar ~label_in_name:false LabelHere vi in
    let pre, (l, r) =
      O.P.allocated ac ~r:vi_region v,
      Pair.map
        ((lo, O.T.offset_min), (ro, O.T.offset_max))
        ~f:(function Some n, _ -> O.T.num n | None, f -> f ac ?r:(Some vi_region) v)
    in
    let instanceof_pre =
      let f = if si.si_final then O.P.typeeq else O.P.instanceof in
      fun p -> f (pointer_class_root pc) ?r:(Some vi_region) p si
    in
    O.P.impl pre O.P.(instanceof_pre v && forall_offset_in_range v l r ~f:(fun p -> [instanceof_pre p]))
  | _ -> True
