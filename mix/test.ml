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

#use "mix_cfg.ml";;

module X = struct
  module Label = struct
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
    let create = let r = ref 0 in fun () -> incr r; "L" ^ string_of_int !r
    let to_string l = l
  end

  type predicate = string
    
  let ptrue = "true"
  let string_of_predicate p = p

  type statement = string
    
  let void_stmt = "void"
  let append_stmt s1 s2 = s1 ^ "; " ^ s2
  let assert_stmt p = "assert " ^ p
  let string_of_stmt s = s

end

include Make(X)

(** test **)

let asm =
  [ Some "init", Aother "k := n";
    None, Ajump "changem";
    Some "loop", Aother "cmp m,X[k]";
    None, Acond ("dec", "assume m >= X[k]", "assume m < X[k]");
    Some "changem", Aother "j := k";
    None, Aother "m := X[k]";
    Some "dec", Aother "k := k-1";
    None, Acond ("loop", "assume k > 0", "assume k <= 0") ]

let cfg,n = make_cfg asm "init"
    
(***
let init = { node_id = 0; node_name = "init"; node_kind = Ninvariant "PRE" }
let changem = { node_id = 1; node_name = "changem"; node_kind = Nassert "" }
let dec = { node_id = 2; node_name = "dec"; node_kind = Nassert "" }
let inv = { node_id = 3; node_name = "inv"; node_kind = Ninvariant "INV" }
let loop = { node_id = 4; node_name = "loop"; node_kind = Nassert "" }
let post = { node_id = 5; node_name = "post"; node_kind = Nassert "POST" }
let g n = match n.node_id with
  | 0 -> [changem, "s1"]
  | 1 -> [dec, "s2"]
  | 2 -> [inv, "s3"]
  | 3 -> [post, "assume r3<=0"; loop, "assume r3>0; s4"]
  | 4 -> [dec, "assume A>=X[r3]"; changem, "assume A<X[r3]"]
  | 5 -> []
  | _ -> assert false

let t = transform g init
***)

