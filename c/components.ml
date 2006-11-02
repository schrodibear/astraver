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

(* $Id: components.ml,v 1.2 2006-11-02 09:18:19 hubert Exp $ *)

module type COMPARABLE = sig 
  type t 
  val compare : t -> t -> int 
  val hash : t -> int 
  val equal : t -> t -> bool
end

module type G = sig
  type t
  module V : COMPARABLE
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
end

module Make(G: G) = struct

  module H = Hashtbl.Make(G.V)
  module S = Set.Make(G.V)

  let scc g =
    let root = H.create 997 in
    let hashcomp = H.create 997 in
    let stack = ref [] in
    let numdfs = ref 0 in
    let numcomp = ref 0 in
    let rec pop x c = function
      | (y, w) :: l when y > x -> 
          H.add hashcomp w !numcomp; 
          pop x (S.add w c) l
      | l -> c,l
    in
    let rec visit v = 
      if not (H.mem root v) then
        begin
          let n = incr numdfs; !numdfs in
          H.add root v n; 
          G.iter_succ 
            (fun w -> 
               visit w;
               if not (H.mem hashcomp w) then 
                 H.replace root v (min (H.find root v) (H.find root w)))
            g v;
          if H.find root v = n then 
            (H.add hashcomp v !numcomp;
             let comp,s = pop n (S.add v S.empty) !stack in 
             stack:= s;
             incr numcomp)
          else stack := (n,v)::!stack;
        end
    in 
    G.iter_vertex visit g;
    ((fun v -> H.find hashcomp v),!numcomp)

  let scc_list g =
    let (scc,_) = scc g in
    let tbl = Hashtbl.create 97 in
    G.iter_vertex 
      (fun v -> 
         let n = scc v in
         try
           let l = Hashtbl.find tbl n in
           l := v :: !l
         with Not_found ->
           Hashtbl.add tbl n (ref [ v ]))
      g;
    Hashtbl.fold (fun _ v l -> !v :: l) tbl []

end
