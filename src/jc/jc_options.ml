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



open Stdlib
open Format
open Env
open Common_options

(* The log file *)

let c = ref stdout

let log =
  c := open_out "jessie.log";
  Format.formatter_of_out_channel !c

let lprintf s = Format.fprintf log s

let close_log () =
  lprintf "End of log.@.";
  close_out !c;
  c := stdout

(* environment variables *)

let libdir =
  try
    let v = Sys.getenv "WHYLIB" in
    lprintf "WHYLIB is set to %s@." v;
    v
  with
  | Not_found ->
    let p = Why_version.libdir in
    lprintf "WHYLIB is not set, using %s as default@." p;
    p

let has_floats = ref false

let float_model : float_model ref = ref FMdefensive

let float_instruction_set : float_instruction_set ref = ref FISstrictIEEE754

let libfiles = ref []

let add_to_libfiles s = libfiles := s :: !libfiles
let get_libfiles () = List.rev !libfiles

(* command-line options *)

let parse_only = ref false
let type_only = ref false
let user_annot_only = ref false
let print_graph = ref false
let why_opt = ref ""
let why3_opt = ref ""

let verify_all_offsets = ref false
let verify_invariants_only = ref false
let verify = ref []
let behavior = ref []

module type Backend = module type of Why_output

let backend = ref (module Why_output : Backend)

let add_why_opt s = why_opt := !why_opt ^ " " ^ s
let add_why3_opt s = why3_opt := !why3_opt ^ " " ^ s

let annotation_sem = ref AnnotNone
let ai_domain = ref AbsNone

let current_rounding_mode = ref FRMNearestEven

let termination_policy = ref Env.TPalways

let int_model = ref IMbounded
let interprocedural = ref false
let main = ref ""
let trust_ai = ref false
let fast_ai = ref false
let forall_inst_bound = ref 10

let gen_frame_rule_with_ft = ref false

let files_ = ref []
let add_file f = files_ := f :: !files_
let files () = List.rev !files_

let pos_files = ref []
let pos_table = Hashtbl.create 97

let version () =
  Printf.printf "This is Jessie version %s, compiled on %s
Copyright (c) 2006-2014 - CNRS/INRIA/Univ Paris-Sud
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
"
    Why_version.version Why_version.date;
  exit 0

let usage = "jessie [options] files"

let _ =
  Arg.parse
      [ "-parse-only", Arg.Set parse_only,
          "  stops after parsing";
        "-type-only", Arg.Set type_only,
          "  stops after typing";
        "-user-annot-only", Arg.Set user_annot_only,
          "  check only user-defined annotations (i.e. safety is assumed)";
        "-print-call-graph", Arg.Set print_graph,
          "  stops after call graph and print call graph";
        "-d", Arg.Set debug,
          "  debugging mode";
        "-locs", Arg.String (fun f -> pos_files := f :: !pos_files),
          "  <f> reads source locations from file f" ;
        "-behavior", Arg.String (fun s -> behavior := s::!behavior),
          "  verify only specified behavior (safety, variant, default or user-defined behavior)";

        "-why3ml", Arg.Unit (fun () -> backend := (module Why3_output)),
          "  (experimental) produce a program in why3ml syntax" ;

        "-why-opt", Arg.String add_why_opt,
          "  <why options>  passes options to Why";
        "-why3-opt", Arg.String add_why3_opt,
          "  <why options>  passes options to Why3";
        "-v", Arg.Set verbose,
          "  verbose mode";
        "-q", Arg.Clear verbose,
          "  quiet mode (default)";
(*      "-ai", Arg.Tuple [                                                          *)
(*        Arg.String (fun s -> ai_domain := s);                                     *)
(*        Arg.Set annot_infer],                                                     *)
(*           "  <box,oct,pol,wp,boxwp,octwp,polwp> performs annotation inference"   *)
(*           ^ " with abstract interpretation using the Box, Octagon"               *)
(*           ^ " or Polyhedron domain, or with weakest preconditions or with both"; *)
        "-forall-inst-bound", Arg.Set_int forall_inst_bound,
          "  bound on the number of expressions resulting from unrolling some forall quantifiers";
        "-main", Arg.Tuple [Arg.Set interprocedural; Arg.Set_string main],
          "  main function for interprocedural abstract interpretation (needs -ai <domain>)";
        "-fast-ai", Arg.Set fast_ai,
          "  fast ai (needs -ai <domain> and -main <function>)";
        "-trust-ai", Arg.Set trust_ai,
          "  verify inferred annotations (needs -ai <domain>)";
        "-separation", Arg.Unit (fun () -> separation_sem := SepRegions),
          "  apply region-based separation on pointers";
        "--werror", Arg.Set werror,
          "  treats warnings as errors";
        "--version", Arg.Unit version,
          "  prints version and exit";
(*
        "-inv-sem", Arg.String
          (function
             | "none" -> inv_sem := InvNone
             | "ownership" -> inv_sem := InvOwnership
             | "arguments" -> inv_sem := InvArguments
             | s -> raise (Arg.Bad ("Unknown mode: "^s))),
          "  <kind>  sets the semantics of invariants (available modes: none, ownership, arguments)";
*)
        "-all-offsets", Arg.Set verify_all_offsets,
          "  generate vcs for all pointer offsets";
        "-invariants-only", Arg.Set verify_invariants_only,
          "  verify invariants only (Arguments policy)";
        "-verify", Arg.String (function s -> verify := s :: !verify),
          "  verify only these functions";
        "-gen_frame_rule_with_ft", Arg.Set gen_frame_rule_with_ft,
        "Experimental : Generate frame rule for predicates and logic functions using only their definitions";
      ]
      add_file usage

let () =
  if !trust_ai && !int_model = IMmodulo then begin
    Format.eprintf "Cannot trust abstract interpretation in modulo integer model";
    exit 1
  end

let usage () =
  eprintf "usage: %s@." usage;
  exit 2

let parse_only = !parse_only
let type_only = !type_only
let user_annot_only = !user_annot_only
let print_graph = !print_graph
let debug = !debug
let verbose = !verbose
let werror = !werror
let backend = !backend
let why_opt = !why_opt
let why3_opt = !why3_opt
let inv_sem = inv_sem
let separation_sem = separation_sem
let trust_ai = !trust_ai
let fast_ai = !fast_ai
let forall_inst_bound = !forall_inst_bound

let verify_all_offsets = !verify_all_offsets
let verify_invariants_only = !verify_invariants_only
let verify = !verify
let interprocedural = !interprocedural
let main = !main
let behavior = !behavior

let gen_frame_rule_with_ft = !gen_frame_rule_with_ft
let () = if gen_frame_rule_with_ft then libfiles := "mybag.why" :: !libfiles

let verify_behavior s =
  behavior = [] || List.mem s behavior

let set_int_model im =
  if im = IMmodulo && trust_ai then begin
    Format.eprintf "cannot trust abstract interpretation in modulo integer model";
    exit 1
  end else
    int_model := im

let set_float_model fm = float_model := fm


(* error handling *)

exception Error of Why_loc.position * string

let jc_error l =
  Format.ksprintf (fun s -> raise @@ Error (l, s))

let jc_warning l =
  Format.kfprintf
    (fun _ -> eprintf "%a: [Warning]: %s@." Why_loc.gen_report_position l @@ flush_str_formatter ())
    str_formatter

let parsing_error l f =
  Format.ksprintf
    (fun s ->
       let s = if s = "" then s else " (" ^ s ^ ")" in
       raise @@ Error (l, "syntax error" ^ s))
    f

(* pos table *)

let kind_of_ident =
  let open Output_ast in
  function
  | "ArithOverflow" -> JCVCarith_overflow
  | "DownCast" -> JCVCdowncast
  | "IndexBounds" -> JCVCpointer_deref_bounds
  | "PointerDeref" -> JCVCpointer_deref
  | "PointerShift" -> JCVCpointer_shift
  | "UserCall" -> JCVCuser_call "?"
  | "DivByZero" -> JCVCdiv_by_zero
  | "AllocSize" -> JCVCalloc_size
  | "Pack" ->  JCVCpack
  | "Unpack" -> JCVCunpack
  | _ -> raise Not_found

let () =
  List.iter
    (fun f ->
       let l = Why_rc.from_file f in
       List.iter
         (fun (id, fs) ->
            let f, l, b, e, k, o =
              List.fold_left
                (fun (f, l, b, e, k, o) v ->
                   let open Why_rc in
                   match v with
                   | "file",  RCstring f -> f, l, b, e, k, o
                   | "line",  RCint l ->    f, l, b, e, k, o
                   | "begin", RCint b ->    f, l, b, e, k, o
                   | "end",   RCint e ->    f, l, b, e, k, o
                   | "kind",  RCident s ->
                     let k = try Some (kind_of_ident s) with Not_found -> None in
                     f, l, b, e, k, o
                   | _ ->
                     f, l, b, e, k, v :: o)
                ("", 0, 0, 0, None, []) fs
            in
            Hashtbl.add pos_table id (f, l, b, e, k, o))
         l)
    !pos_files

let position_of_label name =
  let position f l c = {
    Lexing.pos_fname = f;
    Lexing.pos_lnum = l;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = c;
  } in
  try
    let f, l, b, e, _k, _o = Hashtbl.find pos_table name in
    Some (position f l b, position f l e)
  with Not_found -> None


(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_options.ml"
  End:
*)
