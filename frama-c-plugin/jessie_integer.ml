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



let zero = Int64.zero
let one = Int64.one
let minus_one = Int64.minus_one

let (+) = Int64.add
let (-) = Int64.sub
let ( * ) = Int64.mul
let (/) = Int64.div
let (mod) = Int64.rem
let (~-) = Int64.neg

let max_int = Int64.max_int
let min_int = Int64.min_int

let (land) = Int64.logand
let (lor) = Int64.logor
let (lxor) = Int64.logxor
let (lsl) = Int64.shift_left
let (asr) = Int64.shift_right
let (lsr) = Int64.shift_right_logical

let negative c = c < 0
let nonpositive c = c <= 0
let (<=) i1 i2 = nonpositive (Int64.compare i1 i2)
let (<) i1 i2 = negative (Int64.compare i1 i2)
let (>=) i1 i2 = i2 <= i1
let (>) i1 i2 = i2 < i1

let power_of_two i = 
  assert (i >= 0L && i < 63L);
  1L lsl (Int64.to_int i)

(*
Local Variables:
compile-command: "LC_ALL=C make -C ../.. -j"
End:
*)
