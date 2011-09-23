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

(* wrap treatment on option *)

module Option = struct
  let equal f x1 x2 = match x1,x2 with
    | None,None -> true
    | Some y1,Some y2 -> f y1 y2
    | _ -> false
  (* returns [Some x] iff one argument is [None] and the other is [Some x] *)
  let some x1 x2 = match x1,x2 with
    | None,x | x,None -> x
    | _ -> None
  let app f x = match x with None -> None | Some s -> Some (f s)
  let fold f x y = match x with None -> y | Some s -> f s y
  let binapp f x1 x2 = match x1,x2 with
    | None,_ | _,None -> None
    | Some y1,Some y2 -> Some (f y1 y2)
  let transform f x1 x2 = match x1,x2 with
    | None,None -> None
    | None,Some x | Some x,None -> Some x
    | Some y1,Some y2 -> Some (f y1 y2)
  let pretty f fmt x = match x with
    | None -> ()
    | Some x -> f fmt x
end

(* very basic pair *)

module Pair = struct
  let any f x1 x2 = f x1 || f x2
  let both f x1 x2 = f x1 && f x2

  module Make (L1 : Set.OrderedType) (L2 : Set.OrderedType)
    : Set.OrderedType with type t = L1.t * L2.t =
  struct
    type t = L1.t * L2.t
    let compare x1 x2 =
      let v = L1.compare (fst x1) (fst x2) in
      if (v = 0) then L2.compare (snd x1) (snd x2) else v
  end
end

(* commonly used maps/sets based on std lib *)

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)
module Int32Map = Map.Make (Int32)
module Int32Set = Set.Make (Int32)

(* to avoid warnings about missing cases in pattern-matching,
   when exact form of the list known due to context *)

let list1 l = match l with [a] -> a | _ -> assert false
let list2 l = match l with [a;b] -> a,b | _ -> assert false
let list3 l = match l with [a;b;c] -> a,b,c | _ -> assert false
let list4 l = match l with [a;b;c;d] -> a,b,c,d | _ -> assert false
let list5 l = match l with [a;b;c;d;e] -> a,b,c,d,e | _ -> assert false
