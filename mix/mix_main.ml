
open Format
open Lexing
open Mix_ast
open Mix_seq
open Mix_interp

let report_lb lb =
  let b,e = lexeme_start_p lb, lexeme_end_p lb in
  eprintf "File \"%s\", " b.pos_fname;
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "line %d, characters %d-%d:@\n" l fc lc

let report_loc loc =
  if loc != Lexing.dummy_pos then begin
    eprintf "File \"%s\", " loc.pos_fname;
    let l = loc.pos_lnum in
    let fc = loc.pos_cnum - loc.pos_bol + 1 in
    eprintf "line %d, character %d:@\n" l fc
  end

(* command line *)

let file = ref None
let entry = ref "init"
let gwhy = ref false

let spec = 
  ["-entry", Arg.Set_string entry, "<label>  sets the entry point";
   "-gwhy", Arg.Set gwhy, "  launches gwhy automatically";
  ]
let usage_msg = "demixify [options] file.mix"
let usage () = Arg.usage spec usage_msg; exit 1
let set_file f = match !file with
  | None when Filename.check_suffix f ".mix" -> file := Some f
  | _ -> usage ()
let () = Arg.parse spec set_file usage_msg

let file = match !file with None -> usage () | Some f -> f

(* parsing *)

let pseudo,_ as asm =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  lb.Lexing.lex_curr_p <- {lb.Lexing.lex_curr_p with Lexing.pos_fname = file};
  try
    let asm = Mix_parser.file Mix_lexer.token lb in
    close_in c;
    asm
  with
    | Mix_lexer.Lexical_error s -> 
	report_lb lb; eprintf "Lexical error: %s@." s; exit 1
    | Parsing.Parse_error -> 
	report_lb lb; eprintf "Syntax error@."; exit 1

(* transformation into sequential programs *)

let cl = 
  try 
    sequentialize asm !entry
  with Error (loc, e) ->
    report_loc loc;
    eprintf "%a@." report e;
    exit 1

(* translation to Why code *)

let wl = interp cl

let print_pseudo fmt p = match p.node with
  | Verbatim s -> fprintf fmt "%s@\n@\n" s
  | Equ_addr (id,_) -> fprintf fmt "logic %s : int@\n@\n" id
  | _ -> ()

let print_code fmt = 
  fprintf fmt 
    "(* this file was automatically generated from %s using demixify *)@\n@\n" 
    file;
  List.iter (print_pseudo fmt) pseudo;
  List.iter (print_why_code fmt) wl

let () =
  let ofile = (Filename.chop_extension file) ^ ".why" in
  Pp.print_in_file print_code ofile;
  if !gwhy then 
    let cmd = sprintf "gwhy -lib-file mix.why %s" ofile in
    exit (Sys.command cmd)


