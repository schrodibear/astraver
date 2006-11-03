(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
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

(* $Id: util.ml,v 1.3 2006-11-03 11:55:27 marche Exp $ *)

open Sig

module OTProduct(X: ORDERED_TYPE)(Y: ORDERED_TYPE) = struct 

  type t = X.t * Y.t 

  let compare (x1, y1) (x2, y2) = 
    let cv = X.compare x1 x2 in
    if cv != 0 then cv else Y.compare y1 y2

end

module HTProduct(X: HASHABLE)(Y: HASHABLE) = struct

  type t = X.t * Y.t

  let equal (x1, y1) (x2, y2) =
    X.equal x1 x2 && Y.equal y1 y2

  let hash (x, y) = 
    Hashtbl.hash (X.hash x, Y.hash y)

end

module CMPProduct(X: COMPARABLE)(Y: COMPARABLE) = struct 
  include HTProduct(X)(Y)
  include (OTProduct(X)(Y): sig val compare : t -> t -> int end)
end

module DataV(L : sig type t end)(V : Sig.COMPARABLE) = 
struct
  type data = L.t
  type label = V.t
  type t = data ref * V.t
      
  let compare ((_, x) : t) ((_, x') : t) =
    V.compare x x'
      
  let hash ((_, x) : t) = V.hash x

  let equal ((_, x) : t) ((_, x') : t) = V.equal x x'
				   
  let create y lbl = (ref y, lbl)
  let label (_, z) = z
  let data (y, _) = !y
  let set_data (y, _) = (:=) y
end

