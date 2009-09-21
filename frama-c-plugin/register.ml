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

(* $Id: register.ml,v 1.1 2009-09-08 11:11:43 monate Exp $ *)

(* Import from Cil *)
open Cil_types
open Cil
open Cilutil
open Extlib
module FCAst=Ast
module FCProject=Project
(* Import from Why *)
open Jc
open Jc_ast
open Jc_env
open Jc_fenv
open Jc_pervasives

(* Utility functions *)
open Common

(*
let std_include = Filename.concat Version.datadir "jessie"

let prolog_h_name = Filename.concat std_include "jessie_prolog.h"

let treat_jessie_prolog () =
  Parameters.CppExtraArgs.add ("-include " ^ prolog_h_name)

let treat_jessie_std_headers () =
  Parameters.CppExtraArgs.add ("-I " ^ std_include)
*)

let treat_integer_model () =
  if Jessie_options.IntModel.get_val () = Jessie_options.IMexact then
    Parameters.CppExtraArgs.add ("-D JESSIE_EXACT_INT_MODEL")

let () =
  (* [JS 2009/10/04]
     Preserve the behaviour of svn release <= r5012.
     However it works only if the int-model is set from the command line. *)
  Cmdline.run_after_configuring_stage treat_integer_model

(*
let treat_jessie_no_prolog () =
  Parameters.CppExtraArgs.add ("-D JESSIE_NO_PROLOG")
*)

let apply_if_dir_exist name f =
  try
    let d = Unix.opendir name in
    Unix.closedir d;
    f name
  with Unix.Unix_error (Unix.ENOENT, "opendir",_) -> ()

let run () =
  if Jessie_config.jessie_local then begin
    let whylib = String.escaped (Filename.concat Config.datadir "why") in
    (try ignore (Unix.getenv "WHYLIB")
       (* don't mess needlessly with user settings *)
     with Not_found ->
       apply_if_dir_exist whylib (Unix.putenv "WHYLIB"));
  end;
  Jessie_options.feedback "Starting Jessie translation";
  (* Work in our own project, initialized by a copy of the main one. *)
  let prj =
    File.create_project_from_visitor "jessie"
      (fun prj -> new Visitor.frama_c_copy prj)
  in
  FCProject.copy ~only:(Plugin.get_selection ()) prj;
  FCProject.set_current prj;

  let file = FCAst.get () in

  try
    if file.globals = [] then
      Jessie_options.abort "Nothing to process. There was probably an error before.";
    (* Phase 1: various preprocessing steps before C to Jessie translation *)
    
    (* Enforce the prototype of malloc to exist before visiting anything.
     * It might be useful for allocation pointers from arrays
     *)
    ignore (Common.malloc_function ());
    ignore (Common.free_function ());
    
    (* Rewrite ranges in logic annotations by comprehesion *)
    !Db.Properties.Interp.from_range_to_comprehension
      (Cil.inplace_visit ()) (FCProject.current ()) file;
    if checking then check_types file;
    
    (* Phase 2: C-level rewriting to facilitate analysis *)
    
    Rewrite.rewrite file;
    if checking then check_types file;
    
    if Jessie_options.debug_atleast 1 then print_to_stdout file;
    
    (* Phase 3: Caduceus-like normalization that rewrites C-level AST into
     * Jessie-like AST, still in Cil (in order to use Cil visitors)
     *)
    
    Norm.normalize file;
    Retype.retype file;
    if checking then check_types file;
    
    (* Phase 4: various postprocessing steps, still on Cil AST *)
    
    (* Rewrite ranges back in logic annotations *)
    !Db.Properties.Interp.from_comprehension_to_range
      (Cil.inplace_visit ()) (FCProject.current ()) file;
    
    if Jessie_options.debug_atleast 1 then print_to_stdout file;
    
    (* Phase 5: C to Jessie translation, should be quite straighforward at this
     * stage (after normalization)
     *)
    
    let pragmas = Interp.pragmas file in
    let pfile = Interp.file file in
    
    (* Phase 6: pretty-printing of Jessie program *)
    
    let sys_command cmd =
      if Sys.command cmd <> 0 then
	(Jessie_options.error "Jessie subprocess failed: %s" cmd; raise Exit)
    in
    
    let projname = Jessie_options.ProjectName.get () in
    let projname =
      if projname <> "" then projname else
	match Parameters.Files.get() with
	  | [f] ->
	      (try
		 Filename.chop_extension f
	       with Invalid_argument _ -> f)
	  | _ ->
	      "wholeprogram"
    in
    (* if called on 'path/file.c', projname is 'path/file' *)
    (* jessie_subdir is 'path/file.jessie' *)
    let jessie_subdir = projname ^ ".jessie" in
    Lib.mkdir_p jessie_subdir;
    Jessie_options.feedback "Producing Jessie files in subdir %s" jessie_subdir;
    
    (* basename is 'file' *)
    let basename = Filename.basename projname in
    
    (* filename is 'file.jc' *)
    let filename = basename ^ ".jc" in
    let () = Pp.print_in_file
      (fun fmt ->
	 Jc_output.print_decls fmt pragmas;
	 Format.fprintf fmt "%a" Jc_poutput.pdecls pfile)
      (Filename.concat jessie_subdir filename)
    in
    Jessie_options.feedback "File %s/%s written." jessie_subdir filename;
    
    (* Phase 7: produce source-to-source correspondance file *)
    
    (* locname is 'file.cloc' *)
    let locname = basename ^ ".cloc" in
    Pp.print_in_file Output.print_pos (Filename.concat jessie_subdir locname);
    Jessie_options.feedback "File %s/%s written." jessie_subdir locname;
    
    if Jessie_options.GenOnly.get () then () else
      
      (* Phase 8: call Jessie to Why translation *)
      
      let why_opt =
	Jessie_options.WhyOpt.fold
	  (fun opt acc -> " -why-opt \"" ^ opt ^ "\" " ^ acc) ""
      in
      let jc_opt =
	StringSet.fold (fun opt acc -> " " ^ opt ^ " " ^ acc)
	  (Jessie_options.JcOpt.get ()) ""
      in
      let debug_opt = if Jessie_options.debug_atleast 1 then " -d " else " " in
      let behav_opt =
	if Jessie_options.Behavior.get () <> "" then
	  "-behavior " ^ Jessie_options.Behavior.get ()
	else ""
      in
      let verbose_opt = 
	if Jessie_options.verbose_atleast 1 then " -v " else " " 
      in
      let env_opt =
	if Jessie_options.debug_atleast 1 then
	  "OCAMLRUNPARAM=bt"
	else ""
      in
      let jessie_cmd =
	try Sys.getenv "JESSIEEXEC"
	with Not_found ->
          (* NdV: the test below might not be that useful, since ocaml
             has stack trace in native code since 3.10, even though -g
             is usually missing from native flags.  *)
          if Jessie_options.debug_atleast 1 then
            " jessie.byte "
          else " jessie "
      in
      let cpulimit_opt =
	if Jessie_options.CpuLimit.get () <> 0 then
	  "why-cpulimit " ^ (string_of_int (Jessie_options.CpuLimit.get ()))
	else ""
      in
      let rec make_command = function
	| [] -> ""
	| [ a ] -> a
	| a::cmd -> a ^ " " ^ make_command cmd
      in
      Jessie_options.feedback "Calling Jessie tool in subdir %s" jessie_subdir;
      Sys.chdir jessie_subdir;
      
      
      let cmd =
	make_command
	  [ env_opt; cpulimit_opt; jessie_cmd; "-why-opt -split-user-conj";
	    verbose_opt; why_opt; jc_opt; debug_opt; behav_opt;
	    "-locs"; locname; filename ]
      in
      (*     Format.eprintf "%s" cmd; *)
      sys_command cmd;
      
      (* Phase 9: call Why to VP translation *)
      
      let makefile = basename ^ ".makefile" in
      
      (* temporarily, we launch proving tools of the Why platform,
	 either graphic or script-based
      *)
      
      Jessie_options.feedback "Calling VCs generator.";
      sys_command ("make -f " ^ makefile ^ " " ^ (Jessie_options.Atp.get ()));
      flush_all ()
	
  with Exit -> ()
    
(* ************************************************************************* *)
(* Plug Jessie to the Frama-C platform *)
(* ************************************************************************* *)

let run_and_catch_error () =
  try run ()
  with
    | Unsupported _ as e ->
	warn_general "Unsupported feature(s).@\nJessie plugin can not be used on your code." ;
	if Jessie_options.debug_atleast 1 then raise e else ()
    | NotImplemented _ ->
	warn_general "Not implemented feature(s).
Please submit `feature request' report."
    | Assert_failure(file,a,b) ->
	fatal
	  "Unexpected failure.@\nPlease submit bug report (Ref. \"%s:%d:%d\")."
	  file a b
    | exn ->
	fatal
	  "Unexpected exception.@\nPlease submit bug report (Ref. \"%s\")."
	  (Printexc.to_string exn)

let run_and_catch_error =
  Dynamic.register "Jessie.run_analysis"
    (Type.func Type.unit Type.unit)
    ~journalize:true
    run_and_catch_error

let main _fmt = if Jessie_options.Analysis.get () then run_and_catch_error ()
let () = Db.Main.extend main

(*
Local Variables:
compile-command: "LC_ALL=C make -C ../.."
End:
*)