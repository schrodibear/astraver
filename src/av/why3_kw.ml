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

let is_why3_keyword =
  let ht = Hashtbl.create 43 in
  List.iter (fun kw -> Hashtbl.add ht kw ())
    [
        "as";
        "axiom";
        "clone";
        "else";
        "end";
        "epsilon";
        "exists";
        "export";
        "false";
        "forall";
        "function";
        "goal";
        "if";
        "import";
        "in";
        "inductive";
        "lemma";
        "let";
        "match";
        "meta";
        "namespace";
        "not";
        "predicate";
        "prop";
        "then";
        "theory";
        "true";
        "type";
        "use";
        "with";
        "abstract";
        "absurd";
        "any";
        "assert";
        "assume";
        "begin";
        "check";
        "do";
        "done";
        "downto";
        "exception";
        "for";
        "fun";
        "invariant";
        "label";
        "loop";
        "model";
        "module";
        "mutable";
        "raise";
        "raises";
        "reads";
        "rec";
        "to";
        "try";
        "val";
        "variant";
        "while";
        "writes";
    ];
  Hashtbl.mem ht

