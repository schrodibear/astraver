(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

type t = string * int * int * int

let dummy_position = "", 1, 0, 0

let dummy = dummy_position

let is_dummy = (=) dummy

let of_pos ({ Lexing.pos_fname = f1; pos_lnum = l1; pos_bol = b1; pos_cnum = c1 },
            { Lexing.pos_fname = f2; pos_lnum = l2; pos_bol = b2; pos_cnum = c2 } as pos) =
  if f1 = f2 && l1 >= 1 && l2 >= 1 && l2 >= l1 && c1 - b1 >= 0 && c2 - b2 >= 0 && c2 >= c1 then
    f1, l1, c1 - b1, c2 - c1 + 1
  else if pos = Lexing.(dummy_pos, dummy_pos) then dummy_position
  else invalid_arg "Jc_position.of_pos"

let of_loc (f, l, b, e as loc) =
  if e >= b then f, l, b, e - b + 1
  else if loc = Loc.dummy_floc then dummy_position
  else invalid_arg "Jc_position.of_loc"

let to_loc (f, l, b, n as pos) =
  if pos <> dummy_position then f, l, b, b + n - 1
  else Loc.dummy_floc

let file (f, _, _, _) = f

let line (_, l, _, _) = l

let compare (f1, l1, b1, n1) (f2, l2, b2, n2) =
  let (||=) acc r = if acc <> 0 then acc else r
  and (=?=) = compare in
  f1 =?= f2 ||= l1 =?= l2 ||= b1 =?= b2 ||= n1 =?= n2

let equal pos1 pos2 = compare pos1 pos2 = 0

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_position.ml"
  End:
*)
