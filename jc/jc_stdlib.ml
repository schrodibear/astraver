(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
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

(* $Id: jc_stdlib.ml,v 1.1 2008-08-06 15:17:04 moy Exp $ *)

module Set = struct

  module type OrderedType = Set.OrderedType

  module type S = sig
    include Set.S
    val of_list: elt list -> t
  end

  module Make(Ord : OrderedType) : S with type elt = Ord.t = struct
    include Set.Make(Ord)

    let of_list ls =
      List.fold_left (fun s e -> add e s) empty ls

  end
end

module Map = struct

  module type OrderedType = Map.OrderedType

  module type S = sig
    include Map.S
    val elements: 'a t -> (key * 'a) list
    val keys: 'a t -> key list
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    val merge: ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    val add_merge: ('a -> 'a -> 'a) -> key -> 'a -> 'a t -> 'a t
    val diff_merge: ('a -> 'a -> 'a) -> ('a -> bool) -> 'a t -> 'a t -> 'a t
    val inter_merge: ('a -> 'a -> 'a) -> ('a -> bool) -> 'a t -> 'a t -> 'a t
  end

  module Make(Ord : OrderedType) : S with type key = Ord.t = struct
    include Map.Make(Ord)

    let elements m =
      fold (fun k v acc -> (k,v) :: acc) m []

    let keys m = 
      fold (fun k _v acc -> k :: acc) m []

    let filter f m =
      fold (fun k v m ->
	      if f k v then add k v m else m
	   ) m empty

    let merge f m1 m2 =
      fold (fun k v1 m ->
	      try
		let v2 = find k m2 in
		add k (f v1 v2) m
	      with Not_found ->
		add k v1 m
	   ) m1 m2

    let add_merge f k v m =
      let v = 
	try f v (find k m)
	with Not_found -> v
      in 
      add k v m

    let diff_merge f g m1 m2 =
      fold (fun k v1 m ->
	      try
		let v2 = find k m2 in
		let v = f v1 v2 in
		if g v then m else add k v m
	      with Not_found ->
		add k v1 m
	   ) m1 empty

    let inter_merge f g m1 m2 =
      fold (fun k v1 m ->
	      try
		let v2 = find k m2 in
		let v = f v1 v2 in
		if g v then m else add k v m
	      with Not_found -> m
	   ) m1 empty
	
  end
end

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
