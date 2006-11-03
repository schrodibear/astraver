(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
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

(* $Id: imperative.ml,v 1.3 2006-11-03 11:55:27 marche Exp $ *)

open Sig
open Per_imp

module type S = sig

  (** Imperative Unlabeled Graphs *)
  module Concrete (V: COMPARABLE) : 
    Sig.I with type V.t = V.t and type V.label = V.t and type E.t = V.t * V.t

  (** Abstract Imperative Unlabeled Graphs *)
  module Abstract(V: sig type t end) : Sig.IM with type V.label = V.t

  (** Imperative Labeled Graphs *)
  module ConcreteLabeled (V: COMPARABLE)(E: ORDERED_TYPE_DFT) :
    Sig.I with type V.t = V.t and type V.label = V.t 
	    and type E.t = V.t * E.t * V.t and type E.label = E.t

  (** Abstract Imperative Labeled Graphs *)
  module AbstractLabeled (V: sig type t end)(E: ORDERED_TYPE_DFT) :
    Sig.IM with type V.label = V.t and type E.label = E.t

end

module I = Make(Make_Hashtbl)

type 'a abstract_vertex = { tag : int; label : 'a; mutable mark : int }

(* Implement the module [Mark]. *)
module Make_Mark
  (X: sig 
     type graph
     type label 
     val iter_vertex : (label abstract_vertex -> unit) -> graph -> unit
   end) = 
struct
  type vertex = X.label abstract_vertex
  type graph = X.graph
  let get v = v.mark
  let set v m = v.mark <- m
  let clear g = X.iter_vertex (fun v -> set v 0) g
end

(* Vertex for the abstract imperative graphs. *)
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
    { tag = !cpt_vertex; label = l; mark = 0 }

end

module Digraph = struct

  module Concrete (V: COMPARABLE) = struct

    include I.Digraph.Concrete(V)

    type it = t
    type iv = V.t
    type ie = E.t

    let add_vertex g v = if not (HM.mem v g) then unsafe_add_vertex g v

    let add_edge g v1 v2 = 
      add_vertex g v1;
      add_vertex g v2;
      unsafe_add_edge g v1 v2

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_vertex g v =
      if HM.mem v g then begin
	HM.remove v g;
	HM.iter (fun k s -> HM.add k (S.remove v s) g) g
      end

    let copy = HM.copy

  end

  module ConcreteBidirectional (V: COMPARABLE) = struct

    include I.Digraph.ConcreteBidirectional(V)

    type it = t
    type iv = V.t
    type ie = E.t

    let add_vertex g v = if not (HM.mem v g) then unsafe_add_vertex g v

    let add_edge g v1 v2 = 
      add_vertex g v1;
      add_vertex g v2;
      unsafe_add_edge g v1 v2

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_vertex g v =
      if HM.mem v g then begin
	iter_pred_e ( fun e -> remove_edge_e g e ) g v ;
	iter_succ_e ( fun e -> remove_edge_e g e ) g v ;
	HM.remove v g
      end

    let copy = HM.copy

  end

  module ConcreteLabeled(V: COMPARABLE)(E: ORDERED_TYPE_DFT) = struct

    let default = E.default

    include I.Digraph.ConcreteLabeled(V)(E)

    type it = t
    type iv = V.t
    type ie = E.t

    let add_vertex g v = if not (HM.mem v g) then unsafe_add_vertex g v

    let add_edge_e g (v1, l, v2) = 
      add_vertex g v1;
      add_vertex g v2;
      unsafe_add_edge g v1 (v2, l)

    let add_edge g v1 v2 = add_edge_e g (v1, default, v2)

    let remove_vertex g v =
      if HM.mem v g then
	let remove s =
	  S.fold 
	    (fun (v2, _ as e) s -> if not (V.equal v v2) then S.add e s else s)
	    s S.empty
	in
	HM.remove v g;
	HM.iter (fun k s -> HM.add k (remove s) g) g

    let copy = HM.copy

  end

  module Abstract(V: sig type t end) = struct
    
    include I.Digraph.Abstract(AbstractVertex(V))

    type it = t
    type iv = V.t
    type ie = E.t

    let create () = { edges = create (); size = 0 }

    let add_vertex g v = 
      if not (HM.mem v g.edges) then begin
	g.size <- Pervasives.succ g.size;
	unsafe_add_vertex g.edges v
      end

    let add_edge g v1 v2 = 
      add_vertex g v1;
      add_vertex g v2;
      unsafe_add_edge g.edges v1 v2

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_vertex g v = 
      if HM.mem v g.edges then
	let e = g.edges in
	HM.remove v e;
	HM.iter (fun k s -> HM.add k (S.remove v s) e) e;
	g.size <- Pervasives.pred g.size

    module Mark = Make_Mark(struct 
			      type graph = t 
			      type label = V.label 
			      let iter_vertex = iter_vertex 
			    end)

    let copy g =
      let h = HM.create () in
      let vertex v = 
	try
	  HM.find v h
	with Not_found ->
	  let v' = V.create (V.label v) in
	  HM.add v v' h;
	  v'
      in
      map_vertex vertex g

  end

  module AbstractLabeled(V: sig type t end)(E: ORDERED_TYPE_DFT) = struct
    
    include I.Digraph.AbstractLabeled(AbstractVertex(V))(E)

    type it = t
    type iv = V.t
    type ie = E.t

    let create () = { edges = create (); size = 0 }

    let add_vertex g v = 
      if not (HM.mem v g.edges) then begin
	g.size <- Pervasives.succ g.size;
	unsafe_add_vertex g.edges v
      end

    let add_edge_e g (v1, l, v2) =
      add_vertex g v1;
      add_vertex g v2;
      unsafe_add_edge g.edges v1 (v2, l)

    let add_edge g v1 v2 = add_edge_e g (v1, default, v2)

    let remove_vertex g v =
      if HM.mem v g.edges then
	let remove s =
	  S.fold 
	    (fun (v2, _ as e) s -> if not (V.equal v v2) then S.add e s else s)
	    s S.empty
	in
	let e = g.edges in
	HM.remove v e;
	HM.iter (fun k s -> HM.add k (remove s) e) e;
	g.size <- Pervasives.pred g.size

    module Mark = Make_Mark(struct 
			      type graph = t 
			      type label = V.label 
			      let iter_vertex = iter_vertex 
			    end)

    let copy g =
      let h = HM.create () in
      let vertex v = 
	try
	  HM.find v h
	with Not_found ->
	  let v' = V.create (V.label v) in
	  HM.add v v' h;
	  v'
      in
      map_vertex vertex g

  end

end

module Graph = struct

  module Concrete(V: COMPARABLE) = struct

    module G = Digraph.Concrete(V) 

    include Graph(G)

    (* Export some definitions of [G] *)

    let create = G.create
    let copy = G.copy
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge g v1 v2 = 
      G.add_edge g v1 v2;
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_add_edge g v2 v1

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_edge g v1 v2 =
      G.remove_edge g v1 v2;
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_remove_edge g v2 v1

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

  end

  module ConcreteLabeled (V: COMPARABLE)(E: ORDERED_TYPE_DFT) = struct

    module G = Digraph.ConcreteLabeled(V)(E)

    include Graph(G)

    (* Export some definitions of [G] *)

    let create = G.create
    let copy = G.copy
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge_e g (v1, l, v2 as e) =
      G.add_edge_e g e;
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_add_edge g v2 (v1, l)

    let add_edge g v1 v2 = add_edge_e g (v1, G.default, v2)

    let remove_edge g v1 v2 =
      G.remove_edge g v1 v2;
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_remove_edge g v2 v1

    let remove_edge_e g (v1, l, v2 as e) =
      G.remove_edge_e g e;
      assert (G.HM.mem v1 g && G.HM.mem v2 g);
      G.unsafe_remove_edge_e g (v2, l, v1)

  end

  module Abstract(V: sig type t end) = struct

    module G = Digraph.Abstract(V)

    include Graph(G)

    (* Export some definitions of [G] *)

    module Mark = G.Mark
    let create = G.create
    let copy = G.copy
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge g v1 v2 = 
      G.add_edge g v1 v2;
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      G.unsafe_add_edge g.G.edges v2 v1

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_edge g v1 v2 =
      G.remove_edge g v1 v2;
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      G.unsafe_remove_edge g.G.edges v2 v1

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

  end

  module AbstractLabeled (V: sig type t end)(E: ORDERED_TYPE_DFT) = struct

    module G = Digraph.AbstractLabeled(V)(E)

    include Graph(G)

    (* Export some definitions of [G] *)

    module Mark = G.Mark
    let create = G.create
    let copy = G.copy
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge_e g (v1, l, v2 as e) = 
      G.add_edge_e g e;
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      G.unsafe_add_edge g.G.edges v2 (v1, l)

    let add_edge g v1 v2 = add_edge_e g (v1, G.default, v2)

    let remove_edge g v1 v2 =
      G.remove_edge g v1 v2;
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      G.unsafe_remove_edge g.G.edges v2 v1

    let remove_edge_e g (v1, l, v2 as e) =
      G.remove_edge_e g e;
      assert (G.HM.mem v1 g.G.edges && G.HM.mem v2 g.G.edges);
      G.unsafe_remove_edge_e g.G.edges (v2, l, v1)

  end

end

module Matrix = struct

  module type S = sig
    include Sig.I with type V.t = int and type V.label = int
		  and type E.t = int * int
    val make : int -> t
  end

  module Digraph = struct

    module V = struct
      type t = int
      type label = int
      let compare = Pervasives.compare
      let hash = Hashtbl.hash
      let equal = (==)
      let create i = i
      let label i = i
    end

    module E = struct
      type t = V.t * V.t
      type vertex = V.t
      let compare = Pervasives.compare
      type label = unit
      let create v1 _ v2 = (v1, v2)
      let src = fst
      let dst = snd
      let label _ = ()
    end

    type t = Bitv.t array
    type vertex = V.t
    type edge = E.t

    let create () = 
      failwith "do not use Matrix.create; please use Matrix.make instead"
		      
    let make n =
      if n < 0 then invalid_arg "Matrix.make";
      Array.init n (fun _ -> Bitv.create n false)

    let is_directed = true
			
    let nb_vertex = Array.length
    let is_empty g = nb_vertex g = 0
    let nb_edges =
      Array.fold_left (Bitv.fold_left (fun n b -> if b then n+1 else n)) 0
	
    let mem_vertex g v = 0 <= v && v < nb_vertex g
    let mem_edge g i j = Bitv.get g.(i) j
    let mem_edge_e g (i,j) = Bitv.get g.(i) j
    let find_edge g i j = if mem_edge g i j then i, j else raise Not_found
			       
    (* constructors *)
    let add_edge g i j = Bitv.set g.(i) j true
    let add_edge_e g (i,j) = Bitv.set g.(i) j true
			       
    let remove_edge g i j = Bitv.set g.(i) j false
    let remove_edge_e g (i,j) = Bitv.set g.(i) j false

    let unsafe_add_edge g i j = 
      Bitv.unsafe_set (Array.unsafe_get g i) j true
    let unsafe_remove_edge g i j = 
      Bitv.unsafe_set (Array.unsafe_get g i) j false
				  
    let remove_vertex g _ = ()
    let add_vertex g _ = ()
			   
    let copy g = Array.init (nb_vertex g) (fun i -> Bitv.copy g.(i))
		   
    (* iter/fold on all vertices/edges of a graph *)
    let iter_vertex f g = 
      for i = 0 to nb_vertex g - 1 do f i done
      
    let iter_edges f g =
      for i = 0 to nb_vertex g - 1 do 
	Bitv.iteri (fun j b -> if b then f i j) g.(i)
      done
      
    let fold_vertex f g a = 
      let n = nb_vertex g in 
      let rec fold i a = if i = n then a else fold (i+1) (f i a) in fold 0 a
								      
    let fold_edges f g a =
      fold_vertex
	(fun i a -> 
	   Bitv.foldi_right (fun j b a -> if b then f i j a else a) g.(i) a)
	g a
	
    (* successors and predecessors of a vertex *)
    let succ g i = 
      Bitv.foldi_left (fun l j b -> if b then j::l else l) [] g.(i)
	
    let pred g i = 
      fold_vertex
	(fun j a -> if Bitv.unsafe_get g.(j) i then j :: a else a)
	g []
	
    (* iter/fold on all successor/predecessor of a vertex. *)
    let iter_succ f g i =
      let si = g.(i) in
      for j = 0 to nb_vertex g - 1 do if Bitv.unsafe_get si j then f j done
      (* optimization w.r.t. 
	 [Bitv.iteri (fun j b -> if b then f j) g.(i)]
      *)

    let iter_pred f g i =
      for j = 0 to nb_vertex g - 1 do if Bitv.unsafe_get g.(j) i then f j done
      
    let fold_succ f g i a =
      Bitv.foldi_right (fun j b a -> if b then f j a else a) g.(i) a
	
    let fold_pred f g i a =
      fold_vertex
	(fun j a -> if Bitv.unsafe_get g.(j) i then f j a else a)
	g a
	
    (* degree *)
    let out_degree g i = fold_succ (fun _ n -> n + 1) g i 0
			   
    let in_degree g i = fold_pred (fun _ n -> n + 1) g i 0
			  
    (* map iterator on vertex *)
    let map_vertex f g =
      let n = nb_vertex g in
      let g' = make n in
      iter_edges
	(fun i j -> 
	   let fi = f i in
	   let fj = f j in
	   if fi < 0 || fi >= n || fj < 0 || fj >= n then 
	     invalid_arg "map_vertex";
	   Bitv.unsafe_set g'.(fi) fj true)
	g;
      g'

    (* labeled edges going from/to a vertex *)
    (* successors and predecessors of a vertex *)
    let succ_e g i = 
      Bitv.foldi_left (fun l j b -> if b then (i,j)::l else l) [] g.(i)

    let pred_e g i = 
      fold_vertex
	(fun j a -> if Bitv.unsafe_get g.(j) i then (j,i) :: a else a)
	g []
	
    (* iter/fold on all labeled edges of a graph *)
    let iter_edges_e f g =
      for i = 0 to nb_vertex g - 1 do 
	Bitv.iteri (fun j b -> if b then f (i,j)) g.(i)
      done

    let fold_edges_e f g a =
      fold_vertex
	(fun i a -> 
	   Bitv.foldi_right (fun j b a -> if b then f (i,j) a else a) g.(i) a)
	g a

    (* iter/fold on all edges going from/to a vertex *)
    let iter_succ_e f g i =
      let si = g.(i) in
      for j = 0 to nb_vertex g - 1 do if Bitv.unsafe_get si j then f (i,j) done
      
    let iter_pred_e f g i =
      for j = 0 to nb_vertex g - 1 do 
	if Bitv.unsafe_get g.(j) i then f (j,i) 
      done

    let fold_succ_e f g i a =
      Bitv.foldi_right (fun j b a -> if b then f (i,j) a else a) g.(i) a

    let fold_pred_e f g i a =
      fold_vertex
	(fun j a -> if Bitv.unsafe_get g.(j) i then f (j,i) a else a)
	g a

  end

  module Graph = struct

    module G = Digraph 

    include Per_imp.Graph(G)		 
    (* Export some definitions of [G] *)

    let create = G.create
    let make = G.make
    let copy = G.copy
    let add_vertex = G.add_vertex
    let remove_vertex = G.remove_vertex

    (* Redefine the [add_edge] and [remove_edge] operations *)

    let add_edge g v1 v2 = 
      G.add_edge g v1 v2;
      G.unsafe_add_edge g v2 v1

    let add_edge_e g (v1, v2) = add_edge g v1 v2

    let remove_edge g v1 v2 =
      G.remove_edge g v1 v2;
      G.unsafe_remove_edge g v2 v1

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

  end

end

