(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2009                                               *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jessie_options.mli,v 1.1 2009-09-08 11:11:43 monate Exp $ *)

open Plugin
include Plugin.S

module ProjectName: STRING
module Behavior: STRING
module Analysis: BOOL
module WhyOpt: STRING_SET
module JcOpt: STRING_SET

type int_model = IMexact | IMbounded | IMmodulo
module IntModel: sig
  include STRING
  val get_val: unit -> int_model
end

module GenOnly: BOOL
module SepRegions: BOOL
(*module StdStubs: BOOL*)
module InferAnnot: STRING
module AbsDomain: STRING
module Atp: STRING
module CpuLimit: INT
module HintLevel: INT

(*
Local Variables:
compile-command: "LC_ALL=C make -C ../.."
End:
*)
