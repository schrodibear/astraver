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

module Ast = Av_ast
module Callgraph = Av_callgraph
module Constructors = Av_constructors
module Common_options = Av_common_options
module Env = Av_env
module Effect = Av_effect
module Envset = Av_envset
module Fenv = Av_fenv
module Interp_struct = Av_interp_struct
module Interp_misc = Av_interp_misc
module Interp = Av_interp
module Invariants = Av_invariants
module Iterators = Av_iterators
module Lexer = Av_lexer
module Main = Av_main
module Make = Av_make
module Name = Av_name
module Norm = Av_norm
module Numconst = Av_numconst
module Options = Av_options
module Output = Av_output
module Output_ast = Av_output_ast
module Output_misc = Av_output_misc
module Print_n = Av_print_n
module Print_misc = Av_print_misc
module Print = Av_print
module Pattern = Av_pattern
module Common = Av_common
module Parser = Av_parser
module Position = Av_position
module Print_p = Av_print_p
module Region = Av_region
module Separation = Av_separation
module Stdlib = Av_stdlib
module Struct_tools = Av_struct_tools
module Type_var = Av_type_var
module Typing = Av_typing
module Print_why3 = Av_print_why3
module Version = Av_version

