(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
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

(* $Id: jc_fenv.mli,v 1.25 2008-01-15 14:44:10 marche Exp $ *)

open Jc_env
open Jc_envset
open Jc_region

(* When adding fields for effects, change accordingly function [same_effects]
   in [jc_effect.ml]. *)
type effect =
    {
      jc_effect_alloc_table : StringRegionSet.t;
      jc_effect_tag_table : StringSet.t;
      jc_effect_memories : LogicLabelSet.t FieldRegionMap.t;
      jc_effect_globals : VarSet.t;
      jc_effect_through_params : VarSet.t;
      jc_effect_mutable : StringSet.t;
      jc_effect_committed : StringSet.t;
    }

(* When adding fields for effects, change accordingly function [same_feffects]
   in [jc_effect.ml]. *)
type fun_effect =
    {
      jc_reads : effect;
      jc_writes : effect;
      jc_raises : ExceptionSet.t;
    }

type logic_info =
    {
      jc_logic_info_tag : int;
      jc_logic_info_name : string;
      mutable jc_logic_info_final_name : string;
      mutable jc_logic_info_result_type : jc_type option;
         (*r None for predicates *)
      mutable jc_logic_info_result_region : region;
      mutable jc_logic_info_parameters : var_info list;
      mutable jc_logic_info_param_regions : region list;
      mutable jc_logic_info_effects : effect;
      mutable jc_logic_info_calls : logic_info list;
      mutable jc_logic_info_labels : logic_label list;
    }

type fun_info = {
    jc_fun_info_tag : int;
    jc_fun_info_name : string;
    jc_fun_info_final_name : string;
    jc_fun_info_result : var_info;
    jc_fun_info_return_region : region;
    mutable jc_fun_info_parameters : var_info list;
    mutable jc_fun_info_param_regions : region list;
    mutable jc_fun_info_calls : fun_info list;
    mutable jc_fun_info_logic_apps : logic_info list;
    mutable jc_fun_info_effects : fun_effect;
  }



(*
  Local Variables: 
  compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
  End: 
 *)
