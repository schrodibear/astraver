(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jc_region.ml,v 1.1 2007-12-14 14:28:06 moy Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Format

let dummy_region = 
  {
    jc_reg_variable = false;
    jc_reg_id = 0;
    jc_reg_name = "rdummy";
  }

module InternalRegion = struct

  let count = ref 1 
  let next_count () = let tmp = !count in incr count; tmp

  type t = region

  let make_const name =
    let id = next_count () in
    {
      jc_reg_variable = false;
      jc_reg_id = id;
      jc_reg_name = name ^ (string_of_int id);
    }

  let make_var name =
    let id = next_count () in
    {
      jc_reg_variable = true;
      jc_reg_id = id;
      jc_reg_name = name ^ (string_of_int id);
    }

  let equal r1 r2 = r1.jc_reg_id = r2.jc_reg_id

  let hash r = r.jc_reg_id      

  let name r = r.jc_reg_name

  let variable r = r.jc_reg_variable

end

module UnionFind
  (Elem : sig type t val equal : t -> t -> bool end)
  (ElemTable : Hashtbl.S with type key = Elem.t) =
struct
  
  let table = ElemTable.create 73
  let ranks = ElemTable.create 73

  let rec repr e = 
    try 
      let r = repr(ElemTable.find table e) in
      ElemTable.replace table e r;
      r
    with Not_found -> e

  let rank e =
    try ElemTable.find ranks e with Not_found -> 0

  let unify e1 e2 =
    let r1 = repr e1 and r2 = repr e2 in
    if Elem.equal r1 r2 then ()
    else 
      let k1 = rank r1 and k2 = rank r2 in
      if k1 < k2 then
	ElemTable.replace table r1 r2
      else if k2 < k1 then
	ElemTable.replace table r2 r1
      else 
	begin
	  ElemTable.replace table r1 r2;
	  ElemTable.replace ranks r2 (k2 + 1)
	end
	  
end

module RegionTable = Hashtbl.Make(InternalRegion)

let global_region_table : (InternalRegion.t FieldTable.t) RegionTable.t 
    = RegionTable.create 73

module Region =
struct

  include InternalRegion

  module UF = UnionFind(InternalRegion)(RegionTable)

  let equal r1 r2 =
    InternalRegion.equal (UF.repr r1) (UF.repr r2)

  let rec unify r1 r2 = 
    if equal r1 r2 then () else
      let rep1 = UF.repr r1 and rep2 = UF.repr r2 in
      UF.unify r1 r2;
      let rep = UF.repr r1 in
      let t1 = 
	try RegionTable.find global_region_table rep1 
	with Not_found -> FieldTable.create 0 
      in
      let t2 = 
	try RegionTable.find global_region_table rep2
	with Not_found -> FieldTable.create 0 
      in
      FieldTable.iter 
	(fun fi r1 ->
	  try 
	    begin 
	      let r2 = FieldTable.find t2 fi in
	      unify r1 r2
	    end
	  with Not_found -> FieldTable.add t2 fi r2
	) t1;
      RegionTable.replace global_region_table rep t2

  let make_field r fi =
    let r = UF.repr r in
    try 
      let t = RegionTable.find global_region_table r in
      try FieldTable.find t fi 
      with Not_found -> 
	let fr = make_const fi.jc_field_info_name in
	FieldTable.replace t fi fr;
	fr
    with Not_found ->
      let fr = make_const fi.jc_field_info_name in
      let t = FieldTable.create 5 in
      FieldTable.replace t fi fr;
      RegionTable.replace global_region_table r t;
      fr

end

(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
