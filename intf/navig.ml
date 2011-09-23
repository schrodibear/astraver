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



module type Tree = sig

  type t
  val children : t -> t list

  type info
  val info : t -> info
  val show_info : info -> unit

end

module type NavTree = sig

  type tree
  type t

  val create : tree list -> t

  exception NoMove
  val down : t -> t
  val up : t -> t
  val left : t -> t
  val right : t -> t

  type info
  val info : t -> info
  val show_info : info -> unit

end

module MakeNavTree (T : Tree) = struct

  type tree = T.t

  type t = T.t * move_up * move_left * move_right
  and move_up = Up of (unit -> t)
  and move_left = Left of (unit -> t)
  and move_right = Right of (unit -> t)

  exception NoMove

  let no_move () = raise NoMove

  let up (_, Up f, _, _) = f ()
  let left (_, _, Left f, _) = f ()
  let right (_, _, _, Right f) = f ()

  let rec first_child t = function
    | [] ->
	raise NoMove
    | x :: l ->
	let rec self =
	  x, Up (fun () -> t), Left no_move, 
	  Right (fun () -> sibling (fun () -> t) self l)
	in
	self

  and sibling up ls = function
    | [] ->
	raise NoMove
    | x :: l -> 
	let rec self =
	  x, Up up, Left (fun () -> ls), 
	  Right (fun () -> sibling up self l)
	in
	self

  let down ((x, _, _, _) as t) = first_child t (T.children x)

  let create = function
    | [] ->
	invalid_arg "NavTree.create"
    | x :: l -> 
	let rec self =
	  x, Up no_move, Left no_move, Right (fun () -> sibling no_move self l)
	in
	self

  type info = T.info
  let info (x,_,_,_) = T.info x
  let show_info = T.show_info

end

module MakeNavigator (T : NavTree) = struct

  open T

  let tree = ref None

  let option_iter f = function
    | None -> ()
    | Some t -> f t

  let update () = option_iter (fun t -> show_info (info t)) !tree

  let set t = tree := Some t; update ()

  let move f () = 
    option_iter (fun t -> try set (f t) with NoMove -> ()) !tree

  let down = move T.down
  let up = move T.up
  let left = move T.left
  let right = move T.right

  let next () = 
    let rec really_right t =
      try set (T.right t) with NoMove -> really_right (T.up t)
    in
    option_iter 
      (fun t -> 
	 try set (T.down t) with NoMove -> 
         try set (T.right t) with NoMove ->
	 try really_right (T.up t) with NoMove -> ()) 
      !tree

end
