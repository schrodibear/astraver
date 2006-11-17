(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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

(* $Id: persistent.ml,v 1.1 2006-11-17 17:13:29 moy Exp $ *)

open Sig
open Util
open Per_imp

module type S = sig

  (** Persistent Unlabeled Graphs *)
  module Concrete (V: COMPARABLE) : 
    Sig.P with type V.t = V.t and type V.label = V.t and type E.t = V.t * V.t

  (** Abstract Persistent Unlabeled Graphs *)
  module Abstract(V: sig type t end) : Sig.P with type V.label = V.t

  (** Persistent Labeled Graphs *)
  module ConcreteLabeled (V: COMPARABLE)(E: ORDERED_TYPE_DFT) :
    Sig.P with type V.t = V.t and type V.label = V.t
	    and type E.t = V.t * E.t * V.t and type E.label = E.t

  (** Abstract Persistent Labeled Graphs *)
  module AbstractLabeled (V: sig type t end)(E: ORDERED_TYPE_DFT) :
    Sig.P with type V.label = V.t and type E.label = E.t

end

module P = Make(Make_Map)

type 'a abstract_vertex = { tag : int; label : 'a }

(* Vertex for the abstract persistent graphs. *)
module AbstractVertex(V: sig type t end) = struct

  type label = V.t

  type t = label abstract_vertex

  let compare x y = compare x.tag y.tag 

  let hash x = Hashtbl.hash x.tag

  let equal x y = x.tag == y.tag

  let label x = x.label

  let create l = 
    assert (!cpt_vertex < max_int);
    incr cpt_vertex;
    { tag = !cpt_vertex; label = l }
    
end

module Digraph = struct

  module Concrete (V: COMPARABLE) = struct

    include P.Digraph.Concrete(V)

    let add_vertex g v = if HM.mem v g then g else unsafe_add_vertex g v

    let add_edge g v1 v2 = 
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      unsafe_add_edge g v1 v2

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_vertex g v =
      if HM.mem v g then
	let g = HM.remove v g in
	HM.fold (fun k s g -> HM.add k (S.remove v s) g) g HM.empty
      else
	g

  end

  module ConcreteLabeled(V: COMPARABLE)(E: ORDERED_TYPE_DFT) = struct

    include P.Digraph.ConcreteLabeled(V)(E)

    let add_vertex g v = if HM.mem v g then g else unsafe_add_vertex g v

    let add_edge_e g (v1, l, v2) = 
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      unsafe_add_edge g v1 (v2, l)

    let add_edge g v1 v2 = add_edge_e g (v1, default, v2)

    let remove_vertex g v =
      if HM.mem v g then
	let remove v s =
	  S.fold 
	    (fun (v2, _ as e) s -> if not (V.equal v v2) then S.add e s else s)
	    s S.empty
	in
	let g = HM.remove v g in
	HM.fold (fun k s g -> HM.add k (remove v s) g) g HM.empty
      else
	g

  end

  module Abstract(V: sig type t end) = struct

    include P.Digraph.Abstract(AbstractVertex(V))

    let empty = { edges = empty; size = 0 }

    let add_vertex g v = 
      if HM.mem v g.edges then 
	g 
      else
	{ edges = unsafe_add_vertex g.edges v; size = Pervasives.succ g.size }

    let add_edge g v1 v2 = 
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      { g with edges = unsafe_add_edge g.edges v1 v2 }

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_vertex g v = 
      if HM.mem v g.edges then
	let e = HM.remove v g.edges in
	let e = HM.fold (fun k s g -> HM.add k (S.remove v s) g) e HM.empty in
	{ edges = e; size = Pervasives.pred g.size }
      else
	g

    let remove_edge g v1 v2 = { g with edges = remove_edge g v1 v2 }
    let remove_edge_e g e = { g with edges = remove_edge_e g e }

  end

  module AbstractLabeled(V: sig type t end)(E: ORDERED_TYPE_DFT) = struct

    include P.Digraph.AbstractLabeled(AbstractVertex(V))(E)

    let empty = { edges = empty; size = 0 }

    let add_vertex g v = 
      if HM.mem v g.edges then 
	g 
      else
	{ edges = unsafe_add_vertex g.edges v; size = Pervasives.succ g.size }

    let add_edge_e g (v1, l, v2) = 
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      { g with edges = unsafe_add_edge g.edges v1 (v2, l) }

    let add_edge g v1 v2 = add_edge_e g (v1, default, v2)

    let remove_vertex g v =
      if HM.mem v g.edges then
	let remove v s =
	  S.fold 
	    (fun (v2, _ as e) s -> if not (V.equal v v2) then S.add e s else s)
	    s S.empty
	in
	let edges = HM.remove v g.edges in
	{ edges = 
	    HM.fold (fun k s g -> HM.add k (remove v s) g) edges HM.empty;
	  size = Pervasives.pred g.size }
      else
	g

    let remove_edge g v1 v2 = { g with edges = remove_edge g v1 v2 }
    let remove_edge_e g e = { g with edges = remove_edge_e g e }

  end

end

module Graph = struct

  module Concrete(V: COMPARABLE) = struct

    module G = Digraph.Concrete(V) 

    include Graph(G)

    (* Export some definitions of [G] *)

    let empty = G.empty
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge g v1 v2 = 
      let g = G.add_edge g v1 v2 in
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_add_edge g v2 v1

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_edge g v1 v2 =
      let g = G.remove_edge g v1 v2 in
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_remove_edge g v2 v1

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

  end

  module ConcreteLabeled(V: COMPARABLE)(E: ORDERED_TYPE_DFT) = struct

    module G = Digraph.ConcreteLabeled(V)(E)

    include Graph(G)

    (* Export some definitions of [G] *)

    let empty = G.empty
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge_e g (v1, l, v2 as e) = 
      let g = G.add_edge_e g e in
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_add_edge g v2 (v1, l)

    let add_edge g v1 v2 = add_edge_e g (v1, G.default, v2)

    let remove_edge g v1 v2 =
      let g = G.remove_edge g v1 v2 in
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_remove_edge g v2 v1

    let remove_edge_e g (v1, l, v2 as e) =
      let g = G.remove_edge_e g e in
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_remove_edge_e g (v2, l, v1)

  end

  module Abstract(V: sig type t end) = struct

    module G = Digraph.Abstract(V)

    include Graph(G)

    (* Export some definitions of [G] *)

    let empty = G.empty
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge g v1 v2 = 
      let g = G.add_edge g v1 v2 in
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      { g with G.edges = G.unsafe_add_edge g.G.edges v2 v1 }

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_edge g v1 v2 =
      let g = G.remove_edge g v1 v2 in
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      { g with G.edges = G.unsafe_remove_edge g.G.edges v2 v1 }

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

  end

  module AbstractLabeled (V: sig type t end)(E: ORDERED_TYPE_DFT) = struct

    module G = Digraph.AbstractLabeled(V)(E)

    include Graph(G)

    (* Export some definitions of [G] *)

    let empty = G.empty
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge_e g (v1, l, v2 as e) = 
      let g = G.add_edge_e g e in
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      { g with G.edges = G.unsafe_add_edge g.G.edges v2 (v1, l) }

    let add_edge g v1 v2 = add_edge_e g (v1, G.default, v2)

    let remove_edge g v1 v2 =
      let g = G.remove_edge g v1 v2 in
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      { g with G.edges = G.unsafe_remove_edge g.G.edges v2 v1 }

    let remove_edge_e g (v1, l, v2 as e) =
      let g = G.remove_edge_e g e in
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      { g with G.edges = G.unsafe_remove_edge_e g.G.edges (v2, l, v1) }

  end

end
