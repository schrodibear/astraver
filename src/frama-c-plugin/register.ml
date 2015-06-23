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



(* Import from Cil *)
open Cil_types
open Cil
module FCAst = Ast
module FCProject = Project

(* Utility functions *)
open Common

let std_include = Filename.concat Framac.Config.datadir "jessie"

let treat_jessie_spec_prolog () =
  if Config.Analysis.get () && Config.Specialize.get () then
    let spec_prolog_h_name = Filename.concat std_include Name.File.blockfuns_include in
    Kernel.CppExtraArgs.append_before ["-include " ^ spec_prolog_h_name]

(* The specifications in the lib force Jessie to handle usnupported features e.g. long double *)
let avoid_frama_c_stdlib () =
  if Config.Analysis.get () then
    Kernel.FramaCStdLib.off ()

let () =
  (* [JS 2009/10/04]
     Preserve the behaviour of svn release <= r5012.
     However it works only if the int-model is set from the command line. *)
  (* Extension -- support for specialized memcpy() versions. *)
  List.iter Cmdline.run_after_configuring_stage [treat_jessie_spec_prolog; avoid_frama_c_stdlib]

let steal_globals () =
  let vis =
    object
      inherit Visitor.frama_c_inplace
      method! vglob_aux g =
        match g with
        | GAnnot (a, _) ->
          Annotations.remove_global (Annotations.emitter_of_global a) a;
          Annotations.unsafe_add_global Emitters.jessie a;
          (* SkipChildren is not good, as Annotations.remove_global has
             removed it from AST: we have to re-insert it...
          *)
          ChangeTo [g]
        | _ -> SkipChildren
    end
  in
  Visitor.visitFramacFile vis (FCAst.get ())

let steal_annots () =
  let emitter = Emitters.jessie in
  let l =
    Annotations.fold_all_code_annot
      (fun stmt e ca acc ->
         Annotations.remove_code_annot e stmt ca;
        (stmt, ca) :: acc)
      []
  in
  List.iter (fun (stmt, ca) -> Annotations.add_code_annot emitter stmt ca) l;
  steal_globals ();
  Globals.Functions.iter (Annotations.register_funspec ~emitter ~force:true)

let apply_if_dir_exist name f =
  try
    let d = Unix.opendir name in
    Unix.closedir d;
    f name
  with
  | Unix.Unix_error (Unix.ENOENT, "opendir", _) -> ()

let run () =
  Console.feedback "Starting Jessie translation";
  (* Work in our own project, initialized by a copy of the main one. *)
  let prj =
    File.create_project_from_visitor
      "jessie"
      (new Visitor.frama_c_copy)
  in
  Console.debug "Project created";
  FCProject.copy ~selection:(Parameter_state.get_selection ()) prj;
  FCProject.set_current prj;
  let file = FCAst.get () in
  (* ATTENTION: Hack! *)
  (* Recovering sharing lost somewhere in Frama-C ==> TODO: check upstream Frama-C for this problem *)
  Visitor.visitFramacFile
    (let open Cil_datatype in
     let restore_sharing ~find ~add ~f ?(eff=ignore) h x =
       try
         let x' = find h x in
         if x' != x then begin
           Console.warn_once "This version of Frama-C doesn't respect CIL invariants (sharing is broken)!";
           ChangeDoChildrenPost (f x', Fn.id)
         end else
           DoChildren
       with
       | Not_found ->
         add h x x;
         eff x;
         DoChildren
     in
     object(self)
       inherit Visitor.frama_c_inplace

       val cti = Typeinfo.Hashtbl.create 100
       val cci = Compinfo.Hashtbl.create 100
       val cfi = Fieldinfo.Hashtbl.create 100
       val cei = Enuminfo.Hashtbl.create 100
       val cvi = Varinfo.Hashtbl.create 100

       method! vtype =
         function
         | TNamed (ti, attrs) ->
           Typeinfo.Hashtbl.(restore_sharing ~find ~add ~f:(fun ti -> TNamed (ti, attrs)) cti ti)
         | _ -> DoChildren

       method! vcompinfo =
         let eff ci =
           ci.cfields <-
             List.map
               (fun fi ->
                  match self#vfieldinfo fi with
                  | ChangeDoChildrenPost (fi, _) -> fi
                  | _ -> fi)
               ci.cfields
         in
         Compinfo.Hashtbl.(restore_sharing ~find ~add ~f:Fn.id ~eff cci)
       method! venuminfo = Enuminfo.Hashtbl.(restore_sharing ~find ~add ~f:Fn.id cei)
       method! vfieldinfo fi =
         let eff fi =
           fi.fcomp <-
             (match self#vcompinfo fi.fcomp with
              | ChangeDoChildrenPost (ci, _) -> ci
              | _ -> fi.fcomp)
         in
         Fieldinfo.Hashtbl.(restore_sharing ~find ~add ~f:Fn.id ~eff cfi fi)
       method! vvrbl = Varinfo.Hashtbl.(restore_sharing ~find ~add ~f:Fn.id cvi)
     end)
    file;

  if file.globals = [] then
    Console.abort "Nothing to process. There was probably an error before.";
  (* Phase 1: various preprocessing steps before C to Jessie translation *)

  (* Enforce the prototype of malloc to exist before visiting anything.
   * It might be useful for allocation pointers from arrays.
  *)
  ignore (Ast.Vi.Function.malloc ());
  ignore (Ast.Vi.Function.free ());
  Console.debug  "After malloc and free";
  Debug.check_exp_types file;
  steal_annots ();
  Console.debug "After steal_annots";
  Debug.check_exp_types file;
  (* Extract relevant globals *)
  if Config.Extract.get () then begin
    Console.debug "Extract relevant globals";
    Extractor.extract file;
    Debug.check_exp_types file
  end;
  (* Rewrite ranges in logic annotations by comprehesion *)
  Console.debug "from range to comprehension";
  Rewrite.from_range_to_comprehension (Cil.inplace_visit ()) file;
  Debug.check_exp_types file;

  (* Phase 2: C-level rewriting to facilitate analysis *)

  Rewrite.rewrite file;
  Debug.check_exp_types file;

  (* Phase 3: Caduceus-like normalization that rewrites C-level AST into
   * Jessie-like AST, still in Cil (in order to use Cil visitors)
  *)

  Norm.normalize file;
  Retype.retype file;
  Debug.check_exp_types file;

  (* Phase 4: various postprocessing steps, still on Cil AST *)

  (* Rewrite ranges back in logic annotations *)
  Rewrite.from_comprehension_to_range (Cil.inplace_visit ()) file;
  Debug.check_exp_types  file;

  (* Phase 5: C to Jessie translation, should be quite straighforward at this
   * stage (after normalization)
  *)
  Console.debug "Jessie pragmas";
  let pragmas = Interp.pragmas file in
  Console.debug "Jessie translation";
  let pfile = Interp.file file in
  Console.debug "Printing Jessie program";

  (* Phase 6: pretty-printing of Jessie program *)

  let sys_command cmd =
    if Sys.command cmd <> 0 then
      Console.abort "Jessie subprocess failed: %s" cmd
  in

  let projname = Config.Project_name.get () in
  let projname =
    if projname <> "" then projname
    else
      match Kernel.Files.get() with
      | [f] ->
        (try Filename.chop_extension f with Invalid_argument _ -> f)
      | _ -> "whole_program"
  in
  (* if called on 'path/file.c', projname is 'path/file' *)
  (* jessie_subdir is 'path/file.jessie' *)
  let jessie_subdir = projname ^ ".jessie" in
  let mkdir_p dir =
    if Sys.file_exists dir then begin
      if Unix.((stat dir).st_kind <> S_DIR) then
        failwith ("failed to create directory " ^ dir)
    end else
      Unix.mkdir dir 0o777
  in
  mkdir_p jessie_subdir;
  Console.feedback "Producing Jessie files in subdir %s" jessie_subdir;

  (* basename is 'file' *)
  let basename =
    String.filter_alphanumeric ~assoc:['-', '-'; ' ', '-'; '(', '-'; ')', '-'] ~default:'_' @@
    Filename.basename projname
  in

  (* filename is 'file.jc' *)
  let filename = basename ^ ".jc" in
  Why_pp.print_in_file
    (fun fmt ->
       Jc.Print.print_decls fmt pragmas;
       Format.fprintf fmt "%a" Jc.Print_p.pdecls pfile)
    (Filename.concat jessie_subdir filename);
  Console.feedback "File %s/%s written." jessie_subdir filename;

  (* Phase 7: produce source-to-source correspondance file *)
  (* locname is 'file.cloc' *)
  let locname = basename ^ ".cloc" in
  Why_pp.print_in_file
    Jc.Print.jc_print_pos
    (Filename.concat jessie_subdir locname);
  Console.feedback "File %s/%s written." jessie_subdir locname;

  if not @@ Config.Gen_only.get () then
    (* Phase 8: call Jessie to Why3ML translation *)
    let why3_opt =
      let res = ref "" in
      Config.Why3_opt.iter
        ((:=) res %
         Format.sprintf "%s%s-why-opt %S"
           !res
           (if !res = "" then "" else " "));
      !res
    in
    let jc_opt = Config.Jc_opt.As_string.get () in
    let debug_opt = if Console.debug_at_least 1 then " -d " else " " in
    let behav_opt =
      if Config.Behavior.get () <> "" then
        "-behavior " ^ Config.Behavior.get ()
      else ""
    in
    let verbose_opt =
      if Console.verbose_at_least 1 then " -v " else " "
    in
    let env_opt =
      if Console.debug_at_least 1 then
        "OCAMLRUNPARAM=bt"
      else ""
    in
    let jessie_cmd =
      try Sys.getenv "JESSIEEXEC"
      with
      | Not_found ->
        (* NdV: the test below might not be that useful, since ocaml
           has stack trace in native code since 3.10, even though -g
           is usually missing from native flags.  *)
        if Console.debug_at_least 1 then " jessie.byte "
        else " jessie "
    in
    let timeout =
      if Config.Cpu_limit.get () <> 0 then "TIMEOUT=" ^ (string_of_int (Config.Cpu_limit.get ())) ^ " "
      else ""
    in
    Console.feedback "Calling Jessie tool in subdir %s" jessie_subdir;
    Sys.chdir jessie_subdir;

    let target = Config.Target.get () in
    let jessie_opt =
      match target with
      | "why3" | "why3ml" | "why3ide" | "why3replay" | "why3autoreplay" | "update" -> ""
      | _ -> ""
    in
    let cmd =
      String.concat " "
        [
          env_opt;
          jessie_cmd;
          jessie_opt ;
          verbose_opt;
          why3_opt;
          jc_opt;
          debug_opt;
          behav_opt;
          "-locs";
          locname;
          filename
        ]
    in
    sys_command cmd;

    if target <> "update" then begin
      (* Phase 9: call Why3 to VC translation *)
      let makefile = basename ^ ".makefile" in
      (* temporarily, we launch proving tools of the Why3 platform,
         either graphic or script-based
      *)
      Console.feedback "Calling VCs generator.";
      sys_command (timeout ^ "make -f " ^ makefile ^ " " ^ target)
    end;
    flush_all ()

(* ************************************************************************* *)
(* Plug Jessie to the Frama-C platform *)
(* ************************************************************************* *)

let run_and_catch_error () =
  try run ()
  with
  | Unsupported _ ->
    Console.error "Unsupported feature(s).@\n\
                   Jessie plugin can not be used on your code."
  | Log.FeatureRequest (_, s) ->
    Console.error "Unimplemented feature: %s." s
  | SizeOfError (s, _) when Str.(string_match (regexp "abstract type '\\(.*\\)'") s 0) ->
    Console.error
      "Can't compute the size of an undeclared composite type '%s'"
      (Str.matched_group 1 s)

let run_and_catch_error =
  Dynamic.register
    "run_analysis"
    (Datatype.func Datatype.unit Datatype.unit)
    ~plugin:"Jessie"
    ~journalize:true
    run_and_catch_error

let main () = if Config.Analysis.get () then run_and_catch_error ()
let () = Db.Main.extend main

(*
Local Variables:
compile-command: "LC_ALL=C make"
End:
*)
