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


(*s General options *)

val verbose : bool

val if_verbose : ('a -> unit) -> 'a -> unit
val if_verbose_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_verbose_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val debug : bool

val if_debug : ('a -> unit) -> 'a -> unit
val if_debug_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_debug_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val ocaml : bool
val ocaml_annot : bool
val ocaml_externals : bool

val explain_vc : bool
val locs_table :
  (string, (string * int * int * int * (string * Rc.rc_value) list))
     Hashtbl.t

val wol : bool

val c_file : bool ref

val werror : bool

val parse_only : bool
val type_only : bool
val wp_only : bool

val fast_wp : bool
(*
val black : bool
val white : bool
val wbb : bool
*)
val split_user_conj : bool
val split_bool_op : bool
val lvlmax : int
val all_vc : bool
val eval_goals : bool
val pruning : bool
val pruning_hyp_v : int
val pruning_hyp_p : int
(* Heuristiques en test *)
val prune_coarse_pred_comp : bool
val pruning_hyp_CompInGraph : bool
val pruning_hyp_CompInFiltering : bool
val pruning_hyp_LinkVarsQuantif : bool
val pruning_hyp_keep_single_comparison_representation : bool
val pruning_hyp_comparison_eqOnly : bool
val pruning_hyp_suffixed_comparison : bool
val pruning_hyp_equalities_linked : bool
val pruning_hyp_arithmetic_tactic : bool
val pruning_hyp_var_tactic : int
val pruning_hyp_polarized_preds : bool
val prune_context : bool
val prune_get_depths : bool
val pruning_hyp_considere_arith_comparison_as_special_predicate : bool
(* FIN de Heuristiques en test *)
(*
val modulo : bool
*)

val phantom_types : (string,unit) Hashtbl.t

type expanding = All | Goal | NoExpanding
val defExpanding : expanding
val get_type_expanding : unit -> expanding

type encoding =
  | NoEncoding | Predicates | Stratified | Recursive | Monomorph
  | SortedStratified |MonoInst
val get_types_encoding : unit -> encoding
val set_types_encoding : encoding -> unit

type monoinstWorldGen =
  | MonoinstSorted
  | MonoinstBuiltin
  | MonoinstGoal
  | MonoinstPremises
val monoinstworldgen : monoinstWorldGen
val monoinstoutput_world : bool
val monoinstonlymem : bool
val monoinstnounit : bool
val monoinstonlyconst : bool

type termination = UseVariant | Partial | Total
val termination : termination

(*s Prover options *)

type coq_version = V7 | V8 | V81

type prover =
  | Coq of coq_version | Pvs | HolLight | Mizar | Harvey | Simplify | CVCLite
  | SmtLib | Isabelle | Hol4 | Gappa | Zenon | Z3 | Vampire
  | Ergo | Why | MultiWhy | MultiAltergo | Why3 | Dispatcher | WhyProject

val prover : (* ?ignore_gui:bool  -> *) unit -> prover

val valid : bool
val coq_tactic : string option
val coq_preamble : string
val coq_use_dp: bool

val pvs_preamble : string

val mizar_environ : string option

val isabelle_base_theory : string

val no_simplify_prelude : bool
val simplify_triggers : bool
val no_harvey_prelude : bool
val no_zenon_prelude : bool
val no_cvcl_prelude : bool
val delete_old_vcs : bool

val floats : bool
val show_time : bool

(*s [file f] appends [f] to the directory specified with [-dir], if any *)

val file : string -> string

(* [out_file f] returns the file specified with option -o, or [file f]
   otherwise. This function musn't be used if you want to be able to
   output on stdout *)

val out_file : string -> string

(* If you want to be able to print to stdout transparently you must
   use this function instead of the standard one. *)

val open_out_file : string -> out_channel
val close_out_file : out_channel -> unit
val out_file_exists :  string -> bool

(* [lib_file f] appends [f] to the lib directory *)

val lib_file : string -> string

val lib_dir : string

(*s Files given on the command line *)

val files : string list

(*s GUI? *)

val gui : bool ref
val gui_project : Project.t option ref
val lib_files_to_load : string list

(*
Local Variables:
compile-command: "unset LANG; make -j -C .. bin/why.byte"
End:
*)
