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

open Stdlib
open Ast
open Constructors

open Envset

module type TAst = sig
  type t
  val subs: t -> t list
end

module type TIterators = sig
  type t

  val subs: t -> t list
  val iter: (t -> unit) -> t -> unit

  (* "Parcours en profondeur d'abord, mais l'accumulateur obtenu est ensuite
     passé aussi en largeur." *)
  (** Traverses (folds) the term AST in pre-order.
      Children are traversed in the same order as in the type definitions. *)
  val fold_left: ('a -> t -> 'a) -> 'a -> t -> 'a
  (** Traverses (folds) the term AST in pre-order.
      Children are traversed in the reversed order
      (the inverse of the order they are given in the type definitions). *)
  val fold_right: (t -> 'a -> 'a) -> t -> 'a -> 'a

  (* "Parcours en profondeur avec accumulateur (le même pour tous les fils)." *)
  (** Same as [fold_left], but doesn't pass the accumulator around between children (siblings)
      (updates are only propagated upside-down -- from parents to children). *)
  val iter_deep_left: ('a -> t -> 'a) -> 'a -> t -> unit
  (** Same as [fold_right], but doesn't pass the accumulator around between children (siblings)
      (updates are only propagated upside-down -- from parents to children). *)
  val iter_deep_right: (t -> 'a -> 'a) -> t -> 'a -> unit
end

module Iterators (X: TAst) : TIterators with type t = X.t =
struct
  type t = X.t
  let subs = X.subs
  let rec iter f x = f x; List.iter (iter f) (subs x)
  let rec fold_left f a x =
    let a = f a x in
    List.fold_left (fold_left f) a (subs x)
  let rec fold_right f x a =
    let a = f x a in
    List.fold_right (fold_right f) (subs x) a
  let rec iter_deep_left f a x =
    let a = f a x in
    List.iter (iter_deep_left f a) (subs x)
  let rec iter_deep_right f x a =
    let a = f x a in
    List.iter (fun x -> iter_deep_right f x a) (subs x)
end

(*****************************************************************************)
(* General iterators on parsed expressions.                                  *)
(*****************************************************************************)

type ('a, 'b) small_tuple =
  | Singleton : ('a, 'a) small_tuple
  | Pair : ('a, 'a * 'a) small_tuple
  | Triple : ('a, 'a * 'a * 'a) small_tuple
  | Quadruple : ('a, 'a * 'a * 'a * 'a) small_tuple

let tuple_of_list (type t1) (type t2) : (t1, t2) small_tuple -> t1 list -> t2 =
  fun st l ->
  match st, l with
  | Singleton, [e] -> e
  | Pair, [e1; e2] -> e1, e2
  | Triple, [e1; e2; e3] -> e1, e2, e3
  | Quadruple, [e1; e2; e3; e4] -> e1, e2, e3, e4
  | _ -> failwith "tuple_of_list"

let as1, as2, as3, as4 =
  let f = tuple_of_list in
  f Singleton, f Pair, f Triple, f Quadruple

let pop =
  function
  | e :: r -> e, r
  | _ -> failwith "pop"

let pop_opt opt l =
  Option.map_default ~default:(None, l) ~f:(fun _ -> map_fst (fun e -> Some e) @@ pop l) opt

let rec popn n l =
  if n > 0 then
    let e, r = pop l in
    let es, r = popn (n - 1) r in
    e :: es, r
  else [], l

let replace_sub_pexpr e el =
  let replace_sub_tag tag el =
    let tag_node, el =
      match tag#node with
      | JCPTtag _ | JCPTbottom as tag_node -> tag_node, el
      | JCPTtypeof _e ->
        let e1, el = pop el in
        JCPTtypeof e1, el
    in
    new ptag_with ~node:tag_node tag,el
  in
  let replace_behaviors behs el =
    List.fold_right
      (fun (names, inv, ass) (b, el) ->
         let inv, el = pop_opt inv el in
         (names, inv, ass) :: b, el)
      behs
      ([], el)
  in
  let replace_variant variant el =
    match variant with
    | None -> None, el
    | Some (_, r) -> let v, el = pop el in Some (v, r), el
  in
  let replace_catches catches el =
    List.fold_left
      (fun (acc, el) (id, name, _) ->
         let e1, el = pop el in
         (id, name, e1) :: acc, el)
      ([], el)
      catches
    |> map_fst List.rev
  in
  let replace_cases cases el =
    List.fold_left
      (fun (acc, el) (caselist, _) ->
         let caselist, el =
           List.fold_left
             (fun (acc, el) eopt ->
                let eopt, el = pop_opt eopt el in
                eopt :: acc, el)
             ([], el)
             caselist
           |> map_fst List.rev
         in
         let e1, el = pop el in
         (caselist, e1) :: acc, el)
      ([], el)
      cases
    |> map_fst List.rev
  in
  let (>>=) f1 f2 =
    fun el ->
      let r, el = f1 el in
      f2 r el
  in
  let return r =
    fun el ->
      assert (el == []);
      r
  in
  let do_replace f = f el in
  let enode =
    match e#node with
    | JCPEconst _    | JCPEvar _ | JCPEbreak _
    | JCPEcontinue _ | JCPEgoto _ as enode ->
      enode
    | JCPEeqtype (tag1, tag2) ->
      do_replace (
        replace_sub_tag tag1 >>= fun tag1 ->
        replace_sub_tag tag2 >>= fun tag2 ->
        return @@
      JCPEeqtype (tag1, tag2))
    | JCPEsubtype (tag1, tag2) ->
      do_replace (
        replace_sub_tag tag1 >>= fun tag1 ->
        replace_sub_tag tag2 >>= fun tag2 ->
        return @@
      JCPEsubtype (tag1, tag2))
    | JCPElabel (lab, _) ->
      JCPElabel (lab, as1 el)
    | JCPEbinary (_, bop, _) ->
      let e1, e2 = as2 el in
      JCPEbinary (e1, bop, e2)
    | JCPEunary (uop, _) ->
      JCPEunary (uop, as1 el)
    | JCPEassign (_, _) ->
      let e1, e2 = as2 el in
      JCPEassign (e1, e2)
    | JCPEassign_op (_, op, _) ->
      let e1, e2 = as2 el in
      JCPEassign_op (e1, op, e2)
    | JCPEderef (_, fi) ->
      JCPEderef (as1 el, fi)
    | JCPEapp (fi, labs, _args) ->
      JCPEapp (fi, labs, el)
    | JCPEquantifier (q, ty, labs, trigs, _) ->
      JCPEquantifier (q, ty, labs, trigs, as1 el)
    | JCPEfresh _ ->
      JCPEfresh (as1 el)
    | JCPEold _ ->
      JCPEold (as1 el)
    | JCPEat (_, lab) ->
      JCPEat (as1 el, lab)
    | JCPEoffset (off, _) ->
      JCPEoffset (off, as1 el)
    | JCPEaddress (absolute, _) ->
      JCPEaddress (absolute, as1 el)
    | JCPEbase_block _ ->
      JCPEbase_block (as1 el)
    | JCPEinstanceof (_, st) ->
      JCPEinstanceof (as1 el, st)
    | JCPEcast (_, st) ->
      JCPEcast (as1 el, st)
    | JCPEcast_mod (_, ei) ->
      JCPEcast_mod (as1 el, ei)
    | JCPEif (_, _, _) ->
      let e1, e2, e3 = as3 el in
      JCPEif (e1, e2, e3)
    | JCPErange (e1opt, e2opt) ->
      do_replace (
       pop_opt e1opt >>= fun e1opt ->
       pop_opt e2opt >>= fun e2opt ->
       return @@
      JCPErange (e1opt, e2opt))
    | JCPEmatch (_, ptl) ->
      let e1, el = pop el in
      let ptl = List.map2 (fun (p, _) e -> p, e) ptl el in
      JCPEmatch (e1, ptl)
    | JCPElet (tyopt, name, eopt, _) ->
      let eopt, el = pop_opt eopt el in
      JCPElet (tyopt, name, eopt, as1 el)
    | JCPEdecl (ty, name, eopt) ->
      let eopt, el = pop_opt eopt el in
      assert (el = []);
      JCPEdecl (ty, name, eopt)
    | JCPEalloc (_, name) ->
      JCPEalloc (as1 el, name)
    | JCPEfree _ ->
      JCPEfree (as1 el)
    | JCPEreinterpret (_, st) ->
      JCPEreinterpret (as1 el, st)
    | JCPEmutable (_, tag) ->
      JCPEmutable (as1 el, tag)
    | JCPEblock elist ->
      assert (List.length elist = List.length el);
      JCPEblock el
    | JCPEassert (behav, asrt, _) ->
      JCPEassert (behav, asrt, as1 el)
    | JCPEcontract (req, dec, behs, _) ->
      JCPEcontract (req, dec, behs, as1 el)
    | JCPEwhile (_, behs, variant, _) ->
      do_replace (
        pop >>= fun test ->
        replace_behaviors behs >>= fun behs ->
        replace_variant variant >>= fun variant ->
        fun el ->
      JCPEwhile (test, behs, variant, as1 el))
    | JCPEfor (inits, _, updates, behs, variant, _) ->
      do_replace (
        popn (List.length inits) >>= fun inits ->
        pop >>= fun test ->
        popn (List.length updates) >>= fun updates ->
        replace_behaviors behs >>= fun behs ->
        replace_variant variant >>= fun variant ->
        fun el ->
      JCPEfor (inits, test, updates, behs, variant, as1 el))
    | JCPEreturn _ ->
      JCPEreturn (as1 el)
    | JCPEtry (_, catches, _) ->
      do_replace (
        pop >>= fun body ->
        replace_catches catches >>= fun catches ->
        fun el ->
      JCPEtry (body, catches, as1 el))
    | JCPEthrow (id, _) ->
      JCPEthrow (id, as1 el)
    | JCPEpack (_, id) ->
      JCPEpack (as1 el, id)
    | JCPEunpack (_, id) ->
      JCPEunpack (as1 el, id)
    | JCPEswitch (_, cases) ->
      do_replace (
         pop >>= fun e1 ->
         replace_cases cases >>= fun cases ->
         return @@
     JCPEswitch (e1, cases))
  in
  new pexpr_with ~node:enode e

module PExprAst = struct
  type t = pexpr
  let subtags tag =
    match tag#node with
      | JCPTtag _ | JCPTbottom -> []
      | JCPTtypeof e -> [e]
  let subs e =
    match e#node with
      | JCPEconst _
      | JCPEvar _
      | JCPEbreak _
      | JCPEcontinue _
      | JCPEgoto _
      | JCPErange(None,None)
      | JCPEdecl(_,_,None) ->
          []
      | JCPEeqtype(tag1,tag2) | JCPEsubtype(tag1,tag2) ->
          subtags tag1 @ subtags tag2
      | JCPEassert(_,_,e)
      | JCPElabel(_, e)
      | JCPEderef(e, _)
      | JCPEunary(_, e)
      | JCPEinstanceof(e, _)
      | JCPEcast(e, _)
      | JCPEcast_mod(e, _)
      | JCPEoffset(_, e)
      | JCPEaddress(_,e)
      | JCPEbase_block(e)
      | JCPEalloc(e, _)
      | JCPEfree e
      | JCPEreinterpret (e, _)
      | JCPElet(_, _,None, e)
      | JCPEreturn e
      | JCPEthrow(_, e)
      | JCPEpack(e, _)
      | JCPEunpack(e, _)
      | JCPEfresh e
      | JCPEold e
      | JCPEat(e,_)
      | JCPErange(Some e,None)
      | JCPErange(None,Some e)
      | JCPEdecl(_,_,Some e)
      | JCPEmutable(e,_) ->
          [e]
      | JCPEbinary(e1, _, e2)
      | JCPEassign(e1, e2)
      | JCPEassign_op(e1, _, e2)
      | JCPElet(_, _, Some e1, e2)
      | JCPErange(Some e1,Some e2) ->
          [e1; e2]
      | JCPEif(e1, e2, e3) ->
          [e1; e2; e3]
      | JCPEcontract(_,_,_,e) -> [e]
      | JCPEwhile(e1,behs,variant,body) ->
          let acc =
            List.fold_right
              (fun (_,inv,_ass) acc ->
                 Option.fold ~init:acc ~f:(fun l x -> x :: l) inv
                   (* TODO : ass *))
              behs
              (Option.fold ~init:[body] ~f:(fun l (x,_) -> x :: l) variant)
          in e1::acc
      | JCPEfor(inits,cond,update,behs,variant,body) ->
          let acc =
            List.fold_right
              (fun (_,inv,_ass) acc ->
                 Option.fold ~init:acc ~f:(fun l x -> x :: l) inv
                   (* TODO : ass *))
              behs
              (Option.fold ~init:[body] ~f:(fun l (x, _) -> x :: l) variant)
          in inits @ cond :: update @ acc
      | JCPEblock el
      | JCPEapp(_,_,el) ->
          el
      | JCPEquantifier(_,_,_,_trigs,e) -> [e](*::(List.concat trigs)*)
      | JCPEtry(e1, l, e2) ->
          e1 :: List.map (fun (_, _, e) -> e) l @ [ e2 ]
      | JCPEmatch(e, pel) ->
          e :: List.map snd pel
      | JCPEswitch(e,cases) ->
          let case c =
            List.flatten (List.map (function None -> [] | Some e -> [e]) c)
          in
          e :: List.flatten (List.map (fun (cases,e) -> case cases @ [e]) cases)
end

module IPExpr = Iterators(PExprAst)

let rec map_pexpr ?(before = fun x -> x) ?(after = fun x -> x) e =
  let e = before e in
  let elist = List.map (map_pexpr ~before ~after) (PExprAst.subs e) in
  after (replace_sub_pexpr e elist)


(*****************************************************************************)
(* General iterators on terms.                                               *)
(*****************************************************************************)

type term_subst = Fenv.term Envset.VarMap.t

let rec subst_term (subst : term_subst) t =
  let f = subst_term subst in
  let n = match t#node with
    | JCTconst _ as t1 -> t1
    | JCTvar v as t1 ->
        begin
          try (VarMap.find v subst)#node
          with Not_found -> t1
        end
    | JCTbinary(t1,op,t2) -> JCTbinary(f t1,op,f t2)
    | JCTshift(t1,t2) -> JCTshift(f t1, f t2)
    | JCTrange(t1,t2) -> JCTrange(Option.map f t1, Option.map f t2)
    | JCTunary(op,t1) -> JCTunary(op, f t1)
    | JCTderef(t1,lab,fi) -> JCTderef(f t1,lab,fi)
    | JCTold(t1) -> JCTold(f t1)
    | JCTat(t1,lab) -> JCTat(f t1,lab)
    | JCToffset(kind,t1,st) -> JCToffset(kind,f t1,st)
    | JCTaddress(kind,t1) -> JCTaddress(kind,f t1)
    | JCTbase_block(t1) -> JCTbase_block(f t1)
    | JCTinstanceof(t1,lab,st) -> JCTinstanceof(f t1,lab,st)
    | JCTdowncast (t1, lab, st) -> JCTdowncast (f t1, lab, st)
    | JCTsidecast (t1, lab, st) -> JCTsidecast(f t1, lab, st)
    | JCTrange_cast(t1,ei) -> JCTrange_cast(f t1,ei)
    | JCTrange_cast_mod (t1, ei) -> JCTrange_cast_mod (f t1, ei)
    | JCTreal_cast(t1,rconv) -> JCTreal_cast(f t1,rconv)
    | JCTapp app ->
        JCTapp({app with app_args = List.map f app.app_args})
    | JCTif(t1,t2,t3) -> JCTif(f t1, f t2, f t3)
    | JCTlet(_vi,_t1,_t2) ->
        assert false (* TODO, beware of variable capture *)
    | JCTmatch(_t, _ptl) ->
        assert false (* TODO, beware of variable capture *)
          (* JCTmatch(f t,List.map f ptl) *)
  in
  new term_with ~node:n t

module TermAst = struct
  type t = term
  let subs t =
    match t#node with
      | JCTconst _ | JCTvar _ | JCTrange(None,None) ->
          []
      | JCTbinary(t1,_,t2) | JCTshift(t1,t2)
      | JCTrange(Some t1,Some t2) ->
          [t1;t2]
      | JCTunary (_, t1) | JCTderef (t1, _, _) | JCTold t1 | JCTat (t1, _)
      | JCToffset (_, t1, _) | JCTaddress (_, t1) | JCTbase_block (t1)
      | JCTinstanceof (t1, _, _) | JCTdowncast (t1, _, _) | JCTsidecast (t1, _, _)
      | JCTrange_cast (t1, _) | JCTrange_cast_mod (t1, _)
      | JCTreal_cast (t1, _) | JCTrange (Some t1, None)
      | JCTrange (None, Some t1) ->
          [t1]
      | JCTapp app ->
          app.app_args
      | JCTif(t1,t2,t3) ->
          [t1;t2;t3]
      | JCTmatch(t, ptl) ->
          t :: List.map snd ptl
      | JCTlet(_, t1,t2) ->
          [t1;t2]
end

module ITerm = Iterators(TermAst)


let fold_sub_term it f acc t =
  let it = it f in
  match t#node with
    | JCTconst _
    | JCTvar _ ->
        acc
    | JCTbinary(t1,_,t2)
    | JCTshift(t1,t2) ->
        let acc = it acc t1 in
        it acc t2
    | JCTrange (t1_opt, t2_opt) ->
      Option.fold ~init:acc ~f:it t1_opt |>
      Option.fold_left' ~f:it t2_opt
    | JCTunary (_, t1)
    | JCTderef (t1, _, _)
    | JCTold t1
    | JCToffset (_, t1, _)
    | JCTaddress (_, t1)
    | JCTbase_block (t1)
    | JCTinstanceof (t1, _, _)
    | JCTdowncast (t1, _, _)
    | JCTsidecast (t1, _, _)
    | JCTreal_cast (t1, _)
    | JCTrange_cast (t1, _)
    | JCTrange_cast_mod (t1, _)
    | JCTat (t1, _) ->
        it acc t1
    | JCTapp app ->
        let tl = app.app_args in
        List.fold_left it acc tl
    | JCTif(t1,t2,t3) ->
        let acc = it acc t1 in
        let acc = it acc t2 in
        it acc t3
    | JCTlet(_,t1,t2) ->
        let acc = it acc t1 in
        it acc t2
    | JCTmatch(t, ptl) ->
        let acc = it acc t in
        List.fold_left (fun acc (_, t) -> it acc t) acc ptl

let rec fold_term f acc t =
  let acc = f acc t in
  fold_sub_term fold_term f acc t

let rec fold_rec_term f acc t =
  let cont,acc = f acc t in
  if cont then fold_sub_term fold_rec_term f acc t else acc

let fold_unit f () = f

let iter_term ft t = fold_term (fold_unit ft) () t

let rec map_term f t =
  let tnode = match t#node with
    | JCTconst _ | JCTvar _ | JCTrange (None, None) as tnode -> tnode
    | JCTbinary(t1,bop,t2) ->
        JCTbinary(map_term f t1,bop,map_term f t2)
    | JCTunary(uop,t1) ->
        JCTunary(uop,map_term f t1)
    | JCTshift(t1,t2) ->
        JCTshift(map_term f t1,map_term f t2)
    | JCTderef(t1,lab,fi) ->
        JCTderef(map_term f t1,lab,fi)
    | JCTapp app ->
        let tl = app.app_args in
        JCTapp { app with app_args = List.map (map_term f) tl; }
    | JCTold t ->
        JCTold(map_term f t)
    | JCTat(t,lab) ->
        JCTat(map_term f t,lab)
    | JCToffset(off,t,st) ->
        JCToffset(off,map_term f t,st)
    | JCTaddress(absolute,t) ->
        JCTaddress (absolute,map_term f t)
    | JCTbase_block(t) ->
        JCTbase_block (map_term f t)
    | JCTinstanceof(t,lab,st) ->
        JCTinstanceof(map_term f t,lab,st)
    | JCTdowncast (t, lab, st) ->
        JCTdowncast (map_term f t, lab, st)
    | JCTsidecast (t, lab, st) ->
        JCTsidecast (map_term f t, lab, st)
    | JCTrange_cast(t,ei) ->
        JCTrange_cast(map_term f t,ei)
    | JCTrange_cast_mod (t, ei) ->
        JCTrange_cast_mod (map_term f t, ei)
    | JCTreal_cast(t,rc) ->
        JCTreal_cast(map_term f t,rc)
    | JCTif(t1,t2,t3) ->
        JCTif(map_term f t1,map_term f t2,map_term f t3)
    | JCTlet(vi,t1,t2) ->
        JCTlet(vi,map_term f t1,map_term f t2)
    | JCTrange(Some t1,Some t2) ->
        JCTrange(Some (map_term f t1),Some (map_term f t2))
    | JCTrange(Some t1,None) ->
        JCTrange(Some (map_term f t1),None)
    | JCTrange(None,Some t2) ->
        JCTrange(None,Some (map_term f t2))
    | JCTmatch(t, ptl) ->
        JCTmatch(map_term f t, List.map (fun (p, t) -> p, map_term f t) ptl)
  in
  f (new term_with ~node:tnode t)


(*****************************************************************************)
(* General iterators on assertions.                                          *)
(*****************************************************************************)

let rec iter_term_and_assertion ft fa a =
  let iter_tag tag =
    match tag#node with
      | JCTtag _ | JCTbottom -> ()
      | JCTtypeof(t,_st) -> (* ITerm.iter *) iter_term ft t
  in
  fa a;
  match a#node with
    | JCAtrue | JCAfalse -> ()
    | JCAeqtype(tag1,tag2,_st) | JCAsubtype(tag1,tag2,_st) ->
        iter_tag tag1;
        iter_tag tag2
    | JCArelation(t1,_,t2) ->
        (* ITerm.iter *) iter_term ft t1;
        (* ITerm.iter *) iter_term ft t2
    | JCAapp app ->
        List.iter (iter_term ft) app.app_args
    | JCAfresh t1
    | JCAinstanceof(t1,_,_) | JCAbool_term t1 | JCAmutable(t1,_,_) ->
        iter_term ft t1
    | JCAand al | JCAor al ->
        List.iter (iter_term_and_assertion ft fa) al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) ->
        iter_term_and_assertion ft fa a1;
        iter_term_and_assertion ft fa a2
    | JCAif(t1,a1,a2) ->
        iter_term ft t1;
        iter_term_and_assertion ft fa a1;
        iter_term_and_assertion ft fa a2
    | JCAnot a1 | JCAold a1 | JCAat(a1,_) ->
        iter_term_and_assertion ft fa a1
    | JCAquantifier(_,_,trigs, a1) ->
        List.iter (List.iter (function
                                | JCAPatT t -> iter_term ft t
                                | JCAPatP a -> iter_term_and_assertion ft fa a))
          trigs;
        iter_term_and_assertion ft fa a1
    | JCAlet(_vi,t,p) ->
        iter_term ft t;
        iter_term_and_assertion ft fa p
    | JCAmatch(t, pal) ->
        iter_term ft t;
        List.iter (fun (_, a) -> iter_term_and_assertion ft fa a) pal

(*
let iter_term_and_assertion_in_loop_annot ft fa la =
  List.iter (fun (_behav,inv) ->
               iter_term_and_assertion ft fa inv) la.loop_invariant;
  iter_term_and_assertion ft fa la.loop_free_invariant;
  Option_misc.iter (ITerm.iter ft) la.loop_variant

let iter_term_and_assertion_in_behavior ft fa bv =
  Option_misc.iter (iter_term_and_assertion ft fa) bv.b_assumes;
  (* TODO: assigns *)
  iter_term_and_assertion ft fa bv.b_ensures;
  iter_term_and_assertion ft fa bv.b_free_ensures

let iter_term_and_assertion_in_fun_spec ft fa spec =
  iter_term_and_assertion ft fa spec.fs_requires;
  List.iter (fun (_,_,bv) -> iter_term_and_assertion_in_behavior ft fa bv)
    (spec.fs_default_behavior :: spec.fs_behavior)

let rec fold_assertion f acc a =
  let acc = f acc a in
  match a#node with
    | JCAtrue | JCAfalse | JCArelation _ | JCAapp _ | JCAeqtype _
    | JCAinstanceof _ | JCAbool_term _ | JCAmutable _ | JCAsubtype _ ->
        acc
    | JCAand al | JCAor al ->
        List.fold_left (fold_assertion f) acc al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) | JCAif(_,a1,a2) ->
        let acc = fold_assertion f acc a1 in
        fold_assertion f acc a2
    | JCAnot a1 | JCAquantifier(_,_,a1) | JCAold a1 | JCAat(a1,_) ->
        fold_assertion f acc a1
    | JCAmatch(_, pal) ->
        List.fold_left (fun acc (_, a) -> fold_assertion f acc a) acc pal

(* let fold_term_in_tag f acc tag =  *)
(*   match tag#node with *)
(*     | JCTtag _ | JCTbottom -> acc *)
(*     | JCTtypeof(t,_st) -> fold_term f acc t *)

*)

let fold_sub_term_in_tag it f acc tag =
  match tag#node with
    | JCTtag _ | JCTbottom -> acc
    | JCTtypeof(t,_st) -> it f acc t

let fold_term_in_tag f acc tag =
  fold_sub_term_in_tag fold_term f acc tag

(*

let fold_rec_term_in_tag f acc tag =
  fold_sub_term_in_tag fold_rec_term f acc tag

*)
let rec fold_term_in_assertion f acc a =
  match a#node with
    | JCAtrue | JCAfalse -> acc
    | JCAeqtype(tag1,tag2,_st) | JCAsubtype(tag1,tag2,_st) ->
        let acc = fold_term_in_tag f acc tag1 in
        fold_term_in_tag f acc tag2
    | JCArelation(t1,_,t2) ->
        let acc = fold_term f acc t1 in
        fold_term f acc t2
    | JCAapp app ->
        List.fold_left (fold_term f) acc app.app_args
    | JCAfresh t1
    | JCAinstanceof(t1,_,_) | JCAbool_term t1 | JCAmutable(t1,_,_) ->
        fold_term f acc t1
    | JCAand al | JCAor al ->
        List.fold_left (fold_term_in_assertion f) acc al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) ->
        let acc = fold_term_in_assertion f acc a1 in
        fold_term_in_assertion f acc a2
    | JCAif(t1,a1,a2) ->
        let acc = fold_term f acc t1 in
        let acc = fold_term_in_assertion f acc a1 in
        fold_term_in_assertion f acc a2
    | JCAnot a1 | JCAquantifier(_,_,_,a1) | JCAold a1 | JCAat(a1,_) ->
        fold_term_in_assertion f acc a1
    | JCAlet(_vi,t, p) ->
        let acc = fold_term f acc t in
        fold_term_in_assertion f acc p
    | JCAmatch(t, pal) ->
        let acc = fold_term f acc t in
        List.fold_left (fun acc (_, a) -> fold_term_in_assertion f acc a)
          acc pal

(* let rec fold_term_and_assertion ft fa acc a = *)
(*   let acc = match a#node with *)
(*     | JCAtrue | JCAfalse -> acc *)
(*     | JCAeqtype(tag1,tag2,_st) | JCAsubtype(tag1,tag2,_st) -> *)
(*      let acc = fold_term_in_tag ft acc tag1 in *)
(*      fold_term_in_tag ft acc tag2 *)
(*     | JCArelation(t1,_,t2) ->  *)
(*      let acc = fold_term ft acc t1 in *)
(*      fold_term ft acc t2 *)
(*     | JCAapp app -> *)
(*      List.fold_left (fold_term ft) acc app.app_args *)
(*     | JCAinstanceof(t1,_,_) | JCAbool_term t1 | JCAmutable(t1,_,_) -> *)
(*      fold_term ft acc t1 *)
(*     | JCAand al | JCAor al -> *)
(*      List.fold_left (fold_term_and_assertion ft fa) acc al *)
(*     | JCAimplies(a1,a2) | JCAiff(a1,a2) -> *)
(*      let acc = fold_term_and_assertion ft fa acc a1 in *)
(*      fold_term_and_assertion ft fa acc a2 *)
(*     | JCAif(t1,a1,a2) -> *)
(*      let acc = fold_term ft acc t1 in *)
(*      let acc = fold_term_and_assertion ft fa acc a1 in *)
(*      fold_term_and_assertion ft fa acc a2 *)
(*     | JCAnot a1 | JCAquantifier(_,_,a1) | JCAold a1 | JCAat(a1,_) -> *)
(*      fold_term_and_assertion ft fa acc a1 *)
(*     | JCAmatch(t, pal) -> *)
(*      let acc = fold_term ft acc t in *)
(*      List.fold_left (fun acc (_, a) -> fold_term_and_assertion ft fa acc a) *)
(*        acc pal *)
(*   in *)
(*   fa acc a *)


let rec fold_sub_term_and_assertion itt ita ft fa acc a =
  match a#node with
    | JCAtrue | JCAfalse -> acc
    | JCAeqtype(tag1,tag2,_st) | JCAsubtype(tag1,tag2,_st) ->
        let acc = fold_sub_term_in_tag itt ft acc tag1 in
        fold_sub_term_in_tag itt ft acc tag2
    | JCArelation(t1,_,t2) ->
        let acc = itt ft acc t1 in
        itt ft acc t2
    | JCAapp app ->
        List.fold_left (itt ft) acc app.app_args
    | JCAfresh t1
    | JCAinstanceof(t1,_,_) | JCAbool_term t1 | JCAmutable(t1,_,_) ->
        itt ft acc t1
    | JCAand al | JCAor al ->
        List.fold_left (ita ft fa) acc al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) ->
        let acc = ita ft fa acc a1 in
        ita ft fa acc a2
    | JCAif(t1,a1,a2) ->
        let acc = itt ft acc t1 in
        let acc = ita ft fa acc a1 in
        ita ft fa acc a2
    | JCAnot a1 | JCAold a1 | JCAat(a1,_) ->
        ita ft fa acc a1
    | JCAquantifier(_,_,trigs,a1) ->
        let pat acc = function
          | JCAPatT t -> itt ft acc t
          | JCAPatP a -> ita ft fa acc a in
        let acc = List.fold_left (List.fold_left pat) acc trigs in
        ita ft fa acc a1
    | JCAlet(_vi,t, p) ->
        let acc = itt ft acc t in
        ita ft fa acc p
    | JCAmatch(t, pal) ->
        let acc = itt ft acc t in
        List.fold_left (fun acc (_, a) -> ita ft fa acc a)
          acc pal

let rec fold_term_and_assertion ft fa acc a =
  let acc = fa acc a in
  fold_sub_term_and_assertion fold_term fold_term_and_assertion ft fa acc a

let rec fold_rec_term_and_assertion ft fa acc a =
  let cont,acc = fa acc a in
  if cont then
    fold_sub_term_and_assertion
      fold_rec_term fold_rec_term_and_assertion ft fa acc a
  else acc

(*
let iter_term_and_assertion ft fa a =
  fold_term_and_assertion (fold_unit ft) (fold_unit fa) () a
*)

let fold_sub_location_set itt itls ft fls acc locs =
  let itt = itt ft and itls = itls ft fls in
  match locs#node with
  | JCLSvar _vi ->
    acc
  | JCLSderef (locs, _lab, _fi, _r) ->
    itls acc locs
  | JCLSrange (locs, t1_opt, t2_opt) ->
    itls acc locs |>
    Option.fold_left' ~f:itt t1_opt |>
    Option.fold_left' ~f:itt t2_opt
  | JCLSrange_term (t0, t1_opt, t2_opt) ->
    itt acc t0 |>
    Option.fold_left' ~f:itt t1_opt |>
    Option.fold_left' ~f:itt t2_opt
  | JCLSat (ls, _lab) -> itls acc ls

let rec fold_location_set ft fls acc locs =
  let acc = fls acc locs in
  fold_sub_location_set fold_term fold_location_set ft fls acc locs

let rec fold_rec_location_set ft fls acc locs =
  let cont,acc = fls acc locs in
  if cont then
    fold_sub_location_set fold_rec_term fold_rec_location_set ft fls acc locs
  else acc

(*
let iter_location_set ft fls loc =
  fold_location_set (fold_unit ft) (fold_unit fls) () loc
*)

let fold_sub_location itt itl itls ft fl fls acc loc =
  let itt = itt ft and itl = itl ft fl fls and itls = itls ft fls in
  match loc#node with
    | JCLvar _vi ->
        acc
    | JCLderef (locs,_lab,_fi,_r) ->
        itls acc locs
    | JCLderef_term (locs,_fi) ->
        itt acc locs
    | JCLsingleton t ->
        itt acc t
    | JCLat (loc,_lab) ->
        itl acc loc

let rec fold_location ft fl fls acc loc =
  let acc = fl acc loc in
  fold_sub_location fold_term fold_location fold_location_set ft fl fls acc loc

let rec fold_rec_location ft fl fls acc loc =
  let cont,acc = fl acc loc in
  if cont then
    fold_sub_location fold_rec_term fold_rec_location fold_rec_location_set
      ft fl fls acc loc
  else acc

let iter_location ft fl fls loc =
  fold_location (fold_unit ft) (fold_unit fl) (fold_unit fls) () loc

let fold_sub_behavior _itt ita itl _itls ft fa fl fls acc b =
  let ita = ita ft fa and itl = itl ft fl fls in
  let ita' = Fn.flip ita in
  Option.fold ~init:acc ~f:ita b.b_assumes |>
  Option.fold_left'
      ~f:(fun acc (_,locs) -> List.fold_left itl acc locs)
      b.b_assigns
  |>
  ita' b.b_ensures |>
  ita' b.b_free_ensures

let rec fold_behavior ft fa fl fls acc e =
  fold_sub_behavior
    fold_term fold_term_and_assertion fold_location fold_location_set
    ft fa fl fls acc e

(*
let rec fold_rec_behavior ft fa fl fls acc e =
  fold_sub_behavior
    fold_rec_term fold_rec_term_and_assertion fold_rec_location
    fold_rec_location_set
    ft fa fl fls acc e
*)

(*
let iter_behavior ft fa fl fls b =
  fold_behavior (fold_unit ft) (fold_unit fa) (fold_unit fl) (fold_unit fls)
    () b
*)

let fold_sub_funspec itb _itt ita _itl _itls ft fa fl fls acc spec =
  let ita = ita ft fa and itb = itb ft fa fl fls in
  let acc = ita acc spec.fs_requires in
  let acc = ita acc spec.fs_free_requires in
  List.fold_left
    (fun acc (_pos,_id,behav) -> itb acc behav)
    acc (spec.fs_default_behavior :: spec.fs_behavior)

let fold_funspec ft fa fl fls acc spec =
  fold_sub_funspec
    fold_behavior fold_term fold_term_and_assertion fold_location
    fold_location_set ft fa fl fls acc spec

(*
let rec fold_rec_funspec ft fa fl fls acc spec =
  fold_sub_funspec
    fold_rec_behavior fold_rec_term fold_rec_term_and_assertion
    fold_rec_location fold_rec_location_set ft fa fl fls acc spec

*)
let iter_funspec ft fa fl fls spec =
  fold_funspec (fold_unit ft) (fold_unit fa) (fold_unit fl) (fold_unit fls)
    () spec

let rec map_assertion f a =
  let anode = match a#node with
    | JCAtrue | JCAfalse | JCArelation _ | JCAapp _ | JCAeqtype _
    | JCAinstanceof _ | JCAbool_term _ | JCAmutable _
    | JCAsubtype _ | JCAfresh _ as anode ->
      anode
    | JCAand al ->
      JCAand (List.map (map_assertion f) al)
    | JCAor al ->
      JCAor (List.map (map_assertion f) al)
    | JCAimplies (a1,a2) ->
      JCAimplies (map_assertion f a1,map_assertion f a2)
    | JCAiff (a1,a2) ->
      JCAiff (map_assertion f a1,map_assertion f a2)
    | JCAif (t,a1,a2) ->
      JCAif (t,map_assertion f a1,map_assertion f a2)
    | JCAnot a1 ->
      JCAnot (map_assertion f a1)
    | JCAquantifier (q, vi, trigs, a1) ->
      let trigs =
        List.map
         (List.map @@ function JCAPatT _ as t -> t | JCAPatP a -> JCAPatP (map_assertion f a))
         trigs
      in
      JCAquantifier (q, vi, trigs, map_assertion f a1)
    | JCAold a1 ->
      JCAold (map_assertion f a1)
    | JCAat (a1,lab) ->
      JCAat (map_assertion f a1,lab)
    | JCAmatch (t, pal) ->
      JCAmatch (t, List.map (fun (p, a) -> p, map_assertion f a) pal)
    | JCAlet (vi, t, a) -> JCAlet (vi, t, map_assertion f a)
  in
  f (new assertion_with ~node:anode a)

let map_term_in_tag f tag =
  let tag_node = match tag#node with
    | JCTtag _ | JCTbottom as tag_node -> tag_node
    | JCTtypeof(t,st) ->
        JCTtypeof(map_term f t,st)
  in
  new tag_with ~node:tag_node tag


let rec map_term_in_assertion f a =
  let anode = match a#node with
    | JCAtrue | JCAfalse as anode -> anode
    | JCAeqtype(tag1,tag2,st) ->
        JCAeqtype(map_term_in_tag f tag1,map_term_in_tag f tag2,st)
    | JCAsubtype(tag1,tag2,st) ->
        JCAsubtype(map_term_in_tag f tag1,map_term_in_tag f tag2,st)
    | JCArelation(t1,op,t2) ->
        JCArelation(map_term f t1,op,map_term f t2)
    | JCAapp app ->
        JCAapp { app with app_args = List.map (map_term f) app.app_args }
    | JCAinstanceof(t1,lab,st) ->
        JCAinstanceof(map_term f t1,lab,st)
    | JCAbool_term t1 ->
        JCAbool_term(map_term f t1)
    | JCAfresh t1 ->
        JCAfresh(map_term f t1)
    | JCAmutable(t1,st,tag) ->
        JCAmutable(map_term f t1,st,tag)
    | JCAand al ->
        JCAand(List.map (map_term_in_assertion f) al)
    | JCAor al ->
        JCAor(List.map (map_term_in_assertion f) al)
    | JCAimplies(a1,a2) ->
        JCAimplies
          (map_term_in_assertion f a1,map_term_in_assertion f a2)
    | JCAiff(a1,a2) ->
        JCAiff
          (map_term_in_assertion f a1,map_term_in_assertion f a2)
    | JCAif(t1,a1,a2) ->
        JCAif(
          map_term f t1,
          map_term_in_assertion f a1,
          map_term_in_assertion f a2)
    | JCAnot a1 ->
        JCAnot(map_term_in_assertion f a1)
    | JCAquantifier(q,vi,trigs,a1) ->
        let pat = function
          | JCAPatT t -> JCAPatT (map_term f t)
          | a -> a in
        let trigs = List.map (List.map pat) trigs in
        JCAquantifier(q,vi,trigs,map_term_in_assertion f a1)
    | JCAold a1 ->
        JCAold(map_term_in_assertion f a1)
    | JCAat(a1,lab) ->
        JCAat(map_term_in_assertion f a1,lab)
    | JCAlet(vi, t, p) ->
        JCAlet(vi,map_term f t,map_term_in_assertion f p)
    | JCAmatch(t, pal) ->
        JCAmatch(map_term f t,
                 List.map (fun (p, a) -> p, map_term_in_assertion f a) pal)
  in
  new assertion_with ~node:anode a

let rec map_term_and_assertion fa ft a =
  let anode = match a#node with
    | JCAtrue | JCAfalse as anode -> anode
    | JCAfresh t -> JCAfresh (map_term ft t)
    | JCAlet (vi, t, a) ->
      JCAlet (vi, map_term ft t, map_term_and_assertion fa ft a)
    | JCAeqtype (tag1, tag2, st) ->
      JCAeqtype (map_term_in_tag ft tag1, map_term_in_tag ft tag2, st)
    | JCAsubtype (tag1, tag2, st) ->
      JCAsubtype (map_term_in_tag ft tag1, map_term_in_tag ft tag2, st)
    | JCArelation (t1, op, t2) ->
      JCArelation (map_term ft t1, op, map_term ft t2)
    | JCAapp app ->
      JCAapp { app with app_args = List.map (map_term ft) app.app_args }
    | JCAinstanceof (t1, lab, st) ->
      JCAinstanceof (map_term ft t1, lab, st)
    | JCAbool_term t1 ->
      JCAbool_term (map_term ft t1)
    | JCAmutable (t1, st, tag) ->
      JCAmutable (map_term ft t1, st, tag)
    | JCAand al ->
      JCAand (List.map (map_term_and_assertion fa ft) al)
    | JCAor al ->
      JCAor (List.map (map_term_and_assertion fa ft) al)
    | JCAimplies (a1,a2) ->
      JCAimplies (map_term_and_assertion fa ft a1, map_term_and_assertion fa ft a2)
    | JCAiff (a1, a2) ->
      JCAiff (map_term_and_assertion fa ft a1, map_term_and_assertion fa ft a2)
    | JCAif (t1,a1,a2) ->
      JCAif (map_term ft t1, map_term_and_assertion fa ft a1, map_term_and_assertion fa ft a2)
    | JCAnot a1 ->
      JCAnot (map_term_and_assertion fa ft a1)
    | JCAquantifier (q, vi, trigs, a1) ->
      let trigs =
        List.map
          (List.map @@
            function
            | JCAPatT t -> JCAPatT (map_term ft t)
            | JCAPatP a -> JCAPatP (map_term_and_assertion fa ft a))
          trigs
      in
      JCAquantifier (q, vi, trigs, map_term_and_assertion fa ft a1)
    | JCAold a1 ->
      JCAold (map_term_and_assertion fa ft a1)
    | JCAat (a1,lab) ->
      JCAat (map_term_and_assertion fa ft a1,lab)
    | JCAmatch (t, pal) ->
      JCAmatch (map_term ft t, List.map (fun (p, a) -> p, map_term_and_assertion fa ft a) pal)
  in
  fa (new assertion_with ~node:anode a)

(*****************************************************************************)
(* General iterators on patterns.                                            *)
(*****************************************************************************)


let rec iter_pattern f p =
  f p;
  match p#node with
    | JCPstruct(_, fipl) ->
        List.iter (iter_pattern f) (List.map snd fipl)
    | JCPor(p1, p2) ->
        iter_pattern f p1;
        iter_pattern f p2
    | JCPas(p, _) ->
        iter_pattern f p
    | JCPvar _
    | JCPany
    | JCPconst _ -> ()

(*
let rec fold_pattern f acc p =
  let acc = f acc p in
  match p#node with
    | JCPstruct(_, fipl) ->
        List.fold_left (fold_pattern f) acc (List.rev (List.map snd fipl))
    | JCPor(p1, p2) ->
        let acc = fold_pattern f acc p1 in
        fold_pattern f acc p2
    | JCPas(p, _) ->
        fold_pattern f acc p
    | JCPvar _
    | JCPany
    | JCPconst _ -> ()
*)

(*****************************************************************************)
(* General iterators on expressions.                                         *)
(*****************************************************************************)

let replace_sub_expr e el =
  let as1 = function [e1] -> e1 | _ -> assert false in
  let as2 = function [e1;e2] -> e1,e2 | _ -> assert false in
  let as3 = function [e1;e2;e3] -> e1,e2,e3 | _ -> assert false in
  let pop = function e1::r -> e1,r | _ -> assert false in
  let popopt el = function
    | None -> None,el
    | Some _ -> let e1,r = pop el in Some e1,r
  in
(* dead code
  let rec popn n el =
    if n > 0 then
      let e,r = pop el in
      let el1,el2 = popn (n-1) r in
      e :: el1, el2
    else [],el
  in
*)
  let enode = match e#node with
    | JCEconst _ | JCEvar _ | JCEassert _ | JCEreturn_void as enode -> enode
    | JCEcontract(req,dec,vi_result,behs,_e) ->
        let e1 = as1 el in JCEcontract(req,dec,vi_result,behs,e1)
    | JCEbinary(_e1,bop,_e2) ->
        let e1,e2 = as2 el in JCEbinary(e1,bop,e2)
    | JCEshift(_e1,_e2) ->
        let e1,e2 = as2 el in JCEshift(e1,e2)
    | JCEunary(uop,_e1) ->
        let e1 = as1 el in JCEunary(uop,e1)
    | JCEassign_var(vi,_e2) ->
        let e2 = as1 el in JCEassign_var(vi,e2)
    | JCEassign_heap(_e1,fi,_e2) ->
        let e1,e2 = as2 el in JCEassign_heap(e1,fi,e2)
    | JCEderef(_e1,fi) ->
        let e1 = as1 el in JCEderef(e1,fi)
    | JCEapp call ->
        JCEapp { call with call_args = el }
    | JCEoffset(off,_e,st) ->
        let e1 = as1 el in JCEoffset(off,e1,st)
    | JCEfresh(_e) ->
        let e1 = as1 el in JCEfresh(e1)
    | JCEaddress(absolute,_e) ->
        let e1 = as1 el in JCEaddress(absolute,e1)
    | JCEbase_block(_e) ->
        let e1 = as1 el in JCEbase_block(e1)
    | JCEinstanceof(_e,st) ->
        let e1 = as1 el in JCEinstanceof(e1,st)
    | JCEdowncast (_e, st) ->
      let e1 = as1 el in JCEdowncast (e1, st)
    | JCEsidecast (_e, st) ->
      let e1 = as1 el in JCEsidecast (e1, st)
    | JCEreal_cast(_e,st) ->
        let e1 = as1 el in JCEreal_cast(e1,st)
    | JCErange_cast(_e,st) ->
        let e1 = as1 el in JCErange_cast(e1,st)
    | JCErange_cast_mod (_e, st) ->
        let e1 = as1 el in JCErange_cast_mod (e1, st)
    | JCEif(_e1,_e2,_e3) ->
        let e1,e2,e3 = as3 el in JCEif(e1,e2,e3)
    | JCEmatch(_e1,ptl) ->
        let e1,el = pop el in
        let ptl = List.map2 (fun (p,_e) e -> p,e) ptl el in
        JCEmatch(e1,ptl)
    | JCElet(vi,eopt,_e) ->
        let eopt,el = popopt el eopt in
        let e1 = as1 el in JCElet(vi,eopt,e1)
    | JCEalloc(_e,name) ->
        let e1 = as1 el in JCEalloc(e1,name)
    | JCEfree _e ->
        let e1 = as1 el in JCEfree e1
    | JCEreinterpret (_e, st) ->
        let e1 = as1 el in JCEreinterpret (e1, st)
    | JCEblock elist ->
        assert (List.length elist = List.length el);
        JCEblock el
    | JCEloop(annot,_body) ->
        let body = as1 el in
        JCEloop(annot,body)
    | JCEreturn(ty,_e) ->
        let e1 = as1 el in JCEreturn(ty,e1)
    | JCEtry(_body,catches,_finally) ->
        let body,el = pop el in
        let catches,el =
          List.fold_left (fun (acc,el) (id,name,_e) ->
                            let e1,el = pop el in (id,name,e1)::acc,el
                         ) ([],el) catches
        in
        let catches = List.rev catches in
        let finally = as1 el in
        JCEtry(body,catches,finally)
    | JCEthrow(id,eopt) ->
        let eopt,_el = popopt el eopt in
        JCEthrow(id,eopt)
    | JCEpack(st1,_e,st2) ->
        let e1 = as1 el in JCEpack(st1,e1,st2)
    | JCEunpack(st1,_e,st2) ->
        let e1 = as1 el in JCEunpack(st1,e1,st2)
  in
  new expr_with ~node:enode e

module ExprAst = struct
  type t = Constructors.expr
  let subs e =
    match e#node with
      | JCEconst _
      | JCEvar _
      | JCEassert _
      | JCEreturn_void
      | JCEthrow(_, None) ->
          []
      | JCEderef (e, _)
      | JCEunary (_, e)
      | JCEassign_var (_, e)
      | JCEinstanceof (e, _)
      | JCEdowncast (e, _)
      | JCEsidecast (e, _)
      | JCErange_cast (e, _)
      | JCErange_cast_mod (e, _)
      | JCEreal_cast(e, _)
      | JCEoffset(_, e, _)
      | JCEaddress(_,e)
      | JCEfresh(e)
      | JCEbase_block(e)
      | JCEalloc(e, _)
      | JCEfree e
      | JCEreinterpret (e, _)
      | JCElet(_, None, e)
      | JCEloop(_, e)
      | JCEreturn(_, e)
      | JCEthrow(_, Some e)
      | JCEpack(_, e, _)
      | JCEunpack(_, e, _)
      | JCEcontract(_,_,_,_,e) -> [e]
      | JCEbinary(e1, _, e2)
      | JCEassign_heap(e1, _, e2)
      | JCElet(_, Some e1, e2)
      | JCEshift(e1, e2) ->
          [e1; e2]
      | JCEif(e1, e2, e3) ->
          [e1; e2; e3]
      | JCEblock el ->
          el
      | JCEapp call ->
          call.call_args
      | JCEtry(e1, l, e2) ->
          e1 :: List.map (fun (_, _, e) -> e) l @ [ e2 ]
      | JCEmatch(e, pel) ->
          e :: List.map snd pel
end

module IExpr = Iterators(ExprAst)

let rec map_expr ?(before = fun x -> x) ?(after = fun x -> x) e =
  let e = before e in
  let elist = List.map (map_expr ~before ~after) (ExprAst.subs e) in
  after (replace_sub_expr e elist)

let fold_sub_expr_and_term_and_assertion
    itt ita itl itls ite ft fa fl fls fe acc e =
  let fold_sub_behavior = fold_sub_behavior itt ita itl itls ft fa fl fls in
  let ite = ite ft fa fl fls fe and ita = ita ft fa and itt = itt ft and itl = itl ft fl fls in
  match e#node with
    | JCEconst _
    | JCEvar _
    | JCEreturn_void ->
       acc
    | JCEthrow (_exc, e1_opt) -> Option.fold ~init:acc ~f:ite e1_opt
    | JCEbinary(e1,_,e2)
    | JCEshift(e1,e2)
    | JCEassign_heap(e1,_,e2) ->
        let acc = ite acc e1 in
        ite acc e2
    | JCEunary (_, e1)
    | JCEderef (e1, _)
    | JCEoffset (_, e1, _)
    | JCEaddress (_, e1)
    | JCEbase_block (e1)
    | JCEfresh (e1)
    | JCEdowncast (e1, _)
    | JCEsidecast (e1, _)
    | JCErange_cast(e1,_)
    | JCErange_cast_mod (e1, _)
    | JCEinstanceof(e1,_)
    | JCEreal_cast(e1,_)
    | JCEunpack(_,e1,_)
    | JCEpack(_,e1,_)
    | JCEassign_var(_,e1)
    | JCEalloc(e1,_)
    | JCEfree e1
    | JCEreinterpret (e1, _)
    | JCEreturn(_,e1) ->
        ite acc e1
    | JCElet(_,e1_opt,e2) ->
        ite (Option.fold ~f:ite ~init:acc e1_opt) e2
    | JCEapp call ->
        List.fold_left ite acc call.call_args
    | JCEif(e1,e2,e3) ->
        let acc = ite acc e1 in
        let acc = ite acc e2 in
        ite acc e3
    | JCEmatch(e, ptl) ->
        let acc = ite acc e in
        List.fold_left (fun acc (_, e) -> ite acc e) acc ptl
    | JCEblock el ->
        List.fold_left ite acc el
    | JCEtry(e1,catches,finally) ->
        let acc = ite acc e1 in
        let acc =
          List.fold_left (fun acc (_exc,_vi_opt,e) -> ite acc e) acc catches
        in
        ite acc finally
    | JCEassert(_behav,_asrt,a) ->
        ita acc a
    | JCEloop(la,e1) ->
        let acc = ite acc e1 in
        let acc =
          List.fold_left
            (fun acc (_id,inv, assigns) ->
               Option.fold ~f:ita ~init:acc inv |>
               Option.fold_left' ~f:(List.fold_left itl) assigns
               (* TODO: fold on assigns *))
            acc
            la.loop_behaviors
        in
        let acc = ita acc la.loop_free_invariant in
        Option.fold ~f:(fun acc -> itt acc % fst) ~init:acc la.loop_variant
    | JCEcontract (a_opt, t_opt, _v, behavs, e) ->
      Option.fold ~f:ita ~init:acc a_opt |>
      Option.fold_left' ~f:(fun acc -> itt acc % fst) t_opt |>
      fun acc ->
      let acc =
        List.fold_left
          (fun acc (_loc,_name,behav) ->
             fold_sub_behavior acc behav)
          acc
          behavs
      in
      ite acc e


let rec fold_expr_and_term_and_assertion ft fa fl fls fe acc e =
  let acc = fe acc e in
  fold_sub_expr_and_term_and_assertion
    fold_term fold_term_and_assertion fold_location fold_location_set
    fold_expr_and_term_and_assertion
    ft fa fl fls fe acc e


let rec fold_rec_expr_and_term_and_assertion ft fa fl fls fe acc e =
  let cont,acc = fe acc e in
  if cont then
    fold_sub_expr_and_term_and_assertion
      fold_rec_term fold_rec_term_and_assertion fold_rec_location
      fold_rec_location_set fold_rec_expr_and_term_and_assertion
      ft fa fl fls fe acc e
  else acc

let iter_expr_and_term_and_assertion ft fa fl fls fe e =
  fold_expr_and_term_and_assertion
    (fun () t -> iter_term ft t)
    (fun () a -> iter_term_and_assertion ft fa a)
    (fun () loc -> iter_location ft fl fls loc)
    (fun () ls -> fls ls)
    (fun () e -> fe e) () e


module NExprAst = struct
  type t = nexpr
  let subtags tag =
    match tag#node with
      | JCPTtag _ | JCPTbottom -> []
      | JCPTtypeof e -> [e]
  let subs e =
    match e#node with
      | JCNEconst _
      | JCNEvar _
      | JCNEreturn None
      | JCNEthrow(_, None)
      | JCNErange(None, None) ->
          []
      | JCNEeqtype(tag1,tag2) | JCNEsubtype(tag1,tag2) ->
          subtags tag1 @ subtags tag2
      | JCNElabel(_, e)
      | JCNEderef(e, _)
      | JCNEunary(_, e)
      | JCNEinstanceof(e, _)
      | JCNEcast(e, _)
      | JCNEcast_mod (e, _)
      | JCNEoffset(_, e)
      | JCNEaddress(_,e)
      | JCNEfresh(e)
      | JCNEbase_block(e)
      | JCNEalloc(e, _)
      | JCNEfree e
      | JCNEreinterpret (e, _)
      | JCNElet(_, _, None, e)
      | JCNEassert(_,_,e)
      | JCNEreturn(Some e)
      | JCNEthrow(_, Some e)
      | JCNEpack(e, _)
      | JCNEunpack(e, _)
      | JCNEold e
      | JCNEat(e, _)
      | JCNEmutable(e, _)
      | JCNErange(Some e, None)
      | JCNErange(None, Some e) ->
          [e]
      | JCNEbinary(e1, _, e2)
      | JCNEassign(e1, e2)
      | JCNElet(_, _, Some e1, e2)
      | JCNErange(Some e1, Some e2) ->
          [e1; e2]
      | JCNEcontract(_,_,_,e) ->
          [e]
      | JCNEif(e1, e2, e3) ->
          [e1; e2; e3]
      | JCNEloop(behs, variant, e2) ->
          List.fold_right
            (fun (_, inv, ass) acc ->
               let acc =
                 Option.fold ~f:(fun l x -> x :: l) ~init:acc inv
               in
               Option.fold
                 ~f:(fun l (_,locs) -> locs @ l)
                 ass
                 ~init:acc)
            behs
            (Option.fold ~f:(fun l (x,_) -> x :: l) variant ~init:[e2])
      | JCNEapp(_, _, el)
      | JCNEblock el ->
          el
      | JCNEquantifier(_, _, _, el, e) -> e::(List.concat el)
      | JCNEmatch(e, pel) ->
          e :: List.map snd pel
      | JCNEtry(e1, l, e2) ->
          e1 :: List.map (fun (_, _, e) -> e) l @ [e2]
end

module INExpr = Iterators(NExprAst)

(*
Local Variables:
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End:
*)
