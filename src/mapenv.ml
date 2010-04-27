(********************************************************************************)
(*                                                                              *)
(*  The Why platform for program certification                                  *)
(*                                                                              *)
(*  Copyright (C) 2002-2010                                                     *)
(*                                                                              *)
(*    Yannick MOY, Univ. Paris-sud 11                                           *)
(*    Jean-Christophe FILLIATRE, CNRS                                           *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                                 *)
(*    Romain BARDOU, Univ. Paris-sud 11                                         *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                        *)
(*                                                                              *)
(*  Secondary contributors:                                                     *)
(*                                                                              *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)                *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)              *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)              *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hypothesis pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                             *)
(*                                                                              *)
(*  This software is free software; you can redistribute it and/or              *)
(*  modify it under the terms of the GNU Lesser General Public                  *)
(*  License version 2.1, with the special exception on linking                  *)
(*  described in file LICENSE.                                                  *)
(*                                                                              *)
(*  This software is distributed in the hope that it will be useful,            *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of              *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                        *)
(*                                                                              *)
(********************************************************************************)

open Logic

let rec compare_list cmp l1 l2 =
  match l1,l2 with
    | [],[] -> 0
    | [],_ -> -1
    | _,[] -> 1
    | a1::l1,a2::l2 -> let c = cmp a1 a2 in
      if c<>0 then c
      else compare_list cmp l1 l2

let compare_pair cmp1 cmp2 (id1,l1) (id2,l2) = 
      let c = cmp1 id1 id2 in
      if c<>0 then c
      else cmp2 l1 l2

module PT = 
  struct
    type t = pure_type
    let to_int = function 
      | PTint -> 1
      | PTbool -> 2
      | PTreal -> 3
      | PTunit -> 4
      | PTvar _ -> 5
      | PTexternal _ -> 6

    let rec compare x y =
      let c = Pervasives.compare (to_int x) (to_int y) in
      if c<>0 then c
      else 
        match x,y with
          | PTint, _ | PTbool, _ | PTreal, _ | PTunit, _ -> 0
          | PTvar {tag = t1}, PTvar {tag = t2} -> Pervasives.compare t1 t2
          | PTexternal (l1,id1),PTexternal (l2,id2) -> 
              let c = Ident.I.compare id1 id2 in
              if c<>0 then c
              else compare_list compare l1 l2
          | _ -> assert false
  end

module PT_Map = Map.Make(PT)
module PT_Set = Set.Make(PT)

let rec add_subtype_list s l = 
  List.fold_left (fun s e -> add_subtype s e) s l
and add_subtype s = function
  | PTint | PTbool | PTreal | PTunit | PTvar _ as t -> PT_Set.add t s
  | PTexternal (l,_id) as t -> add_subtype_list (PT_Set.add t s) l

let _PT_Set_add_normalize x s = PT_Set.add (Misc.normalize_pure_type x) s

(* pair string,instance *)
module Inst =
  struct
    type t = Ident.t * instance
    let compare = compare_pair Ident.I.compare (compare_list PT.compare)
  end
        
module Inst_Map = Map.Make(Inst)
        
let fold_map f acc l =
  let acc,l = List.fold_left (fun (acc,l) e -> 
                                let acc,e = (f acc e) in
                                acc,e::l) (acc,[]) l in
  acc,List.rev l
  
     

