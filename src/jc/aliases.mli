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
(*  Jessie2 fork:                                                         *)
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

module Ai = Jc_ai
module Ast = Jc_ast
module Annot_inference = Jc_annot_fail
module Callgraph = Jc_callgraph
module Common_options = Jc_common_options
module Constructors = Jc_constructors
module Env = Jc_env
module Effect = Jc_effect
module Envset = Jc_envset
module Fenv = Jc_fenv
module Frame = Jc_frame
module Frame_notin = Jc_frame_notin
module Interp_struct = Jc_interp_struct
module Interp_misc = Jc_interp_misc
module Interp = Jc_interp
module Invariants = Jc_invariants
module Iterators = Jc_iterators
module Lexer = Jc_lexer
module Main = Jc_main
module Make = Jc_make
module Name = Jc_name
module Norm = Jc_norm
module Numconst = Jc_numconst
module Print_n = Jc_print_n
module Options = Jc_options
module Print_misc = Jc_print_misc
module Print = Jc_print
module Pattern = Jc_pattern
module Common = Jc_common
module Parser = Jc_parser
module Position = Jc_position
module Print_p = Jc_print_p
module Region = Jc_region
module Separation = Jc_separation
module Stdlib = Jc_stdlib
module Struct_tools = Jc_struct_tools
module Type_var = Jc_type_var
module Typing = Jc_typing
module Print_why3 = Jc_print_why3
module Why_output = Jc_why_output
module Output_ast = Jc_output_ast
module Output = Jc_output
module Output_misc = Jc_output_misc
