(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
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
(*  AstraVer fork:                                                        *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

type t = (string * int * int * int) option

let dummy_position = None

let dummy = dummy_position

let is_dummy = (=) dummy

let of_pos ({ Lexing.pos_fname = f1; pos_lnum = l1; pos_bol = b1; pos_cnum = c1 },
            { Lexing.pos_fname = f2; pos_lnum = l2; pos_bol = b2; pos_cnum = c2 } as pos) =
  if f1 = f2 && l1 >= 1 && l2 >= 1 && l2 >= l1 && c1 - b1 >= 0 && c2 - b2 >= 0 && c2 >= c1 then
    Some (f1, l1, c1 - b1, c2 - c1 + 1)
  else if pos = Lexing.(dummy_pos, dummy_pos) then dummy_position
  else invalid_arg "Position.of_pos"

let of_loc (f, l, b, e as loc) =
  if e >= b then Some (f, l, b, e - b + 1)
  else if loc = Why_loc.dummy_floc then dummy_position
  else invalid_arg "Position.of_loc"

let to_loc =
  function
  | Some (f, l, b, n) ->
    f, l, b, b + n - 1
  | None -> Why_loc.dummy_floc

let file =
  function
  | Some (f, _, _, _) -> Some f
  | None -> None

let line =
  function
  | Some (_, l, _, _) -> Some l
  | None -> None

let compare pos1 pos2 =
  match pos1, pos2 with
  | None, _ -> 1
  | _, None -> -1
  | Some (f1, l1, b1, n1), Some (f2, l2, b2, n2) ->
    let (||) acc r = if acc <> 0 then acc else r
    and (=?=) = compare in
    f1 =?= f2 || l1 =?= l2 || b1 =?= b2 || n1 =?= n2

let equal pos1 pos2 = compare pos1 pos2 = 0

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_position.ml"
  End:
*)
