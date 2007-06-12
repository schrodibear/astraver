
open Format
open Lexing
open Mix_ast
open Mix_seq

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

let asm =
  let f = Sys.argv.(1) in
  let c = open_in f in
  let lb = Lexing.from_channel c in
  lb.Lexing.lex_curr_p <- { lb.Lexing.lex_curr_p with Lexing.pos_fname = f };
  try
    let asm = Mix_parser.file Mix_lexer.token lb in
    close_in c;
    asm
  with
    | Mix_lexer.Lexical_error s -> 
	report_lb lb; eprintf "Lexical error: %s@." s; exit 1
    | Parsing.Parse_error -> 
	report_lb lb; eprintf "Syntax error@."; exit 1

let cl = 
  try 
    interp asm Sys.argv.(2)
  with Error (loc, e) ->
    report_loc loc;
    eprintf "%a@." report e;
    exit 1

let print_seq_code fmt c = 
  begin match c.seq_pre with
    | Some p -> fprintf fmt "pre { %s }@\n" (X.string_of_predicate p)
    | None -> ()
  end;
  fprintf fmt "code %s@\n@\n" (X.string_of_stmt c.seq_code)

let () = List.iter (print_seq_code std_formatter) cl


