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

(* $Id: topological.mli,v 1.2 2006-11-02 09:18:21 hubert Exp $ *)

(** Topological order.

  This functor provides functions which allow iterating over a
  directed graph in topological order *)

(** Minimal graph signature to provide *)
module type G = sig
  type t
  module V : Sig.HASHABLE
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val in_degree : t -> V.t -> int
end

module Make(G: G) : sig

  val fold : (G.V.t -> 'a -> 'a) -> G.t -> 'a -> 'a
    (** [fold action g seed] allows iterating over the graph [g] 
      in topological order. [action node accu] is called repeatedly,
      where [node] is the node being visited, and [accu] is the result of 
      the [action]'s previous invocation, if any, and [seed] otherwise. *)

  val iter : (G.V.t -> unit) -> G.t -> unit
    (** [iter action] calls [action node] repeatedly. Nodes are (again) 
      presented to [action] in topological order. *)

end


