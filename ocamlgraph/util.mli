(*
 * Graph: generic graph library
 * Copyright (C) 2004
 * Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(* $Id: util.mli,v 1.2 2006-11-02 09:18:22 hubert Exp $ *)

open Sig

module OTProduct(X: ORDERED_TYPE)(Y: ORDERED_TYPE) : 
  ORDERED_TYPE with type t = X.t * Y.t

module HTProduct(X: HASHABLE)(Y: HASHABLE) :
  HASHABLE with type t = X.t * Y.t

module CMPProduct(X: COMPARABLE)(Y: COMPARABLE) : 
  COMPARABLE with type t = X.t * Y.t

(** Create a vertex type with some data attached to it *)
module DataV 
  (L : sig type t end)
  (V : Sig.COMPARABLE) :
sig
  type data = L.t
  and label = V.t
  and t = data ref * V.t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
  val create : data -> V.t -> t
  val label : t -> V.t
  val data : t -> data
  val set_data : t -> data -> unit
end
  
