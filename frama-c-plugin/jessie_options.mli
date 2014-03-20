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

include Plugin.S

module ProjectName: Parameter_sig.String
module Behavior: Parameter_sig.String
module Analysis: Parameter_sig.Bool
module WhyOpt: Parameter_sig.String_set
module Why3Opt: Parameter_sig.String_set
module JcOpt: Parameter_sig.String_set
module GenOnly: Parameter_sig.Bool
module InferAnnot: Parameter_sig.String
module AbsDomain: Parameter_sig.String
module Atp: Parameter_sig.String
module CpuLimit: Parameter_sig.Int
module HintLevel: Parameter_sig.Int
module SpecBlockFuncs : Parameter_sig.Bool
module VoidSupertype : Parameter_sig.Bool
module Extract : Parameter_sig.Bool
module FlatVararg : Parameter_sig.Bool

(*
Local Variables:
compile-command: "LC_ALL=C make"
End:
*)
