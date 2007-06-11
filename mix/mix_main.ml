
open Format
open Lexing
open Mix_ast

module X = struct
  module Label = struct
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
    let create = let r = ref 0 in fun () -> incr r; "L" ^ string_of_int !r
    let to_string l = l
  end

  type predicate = string
    
  let ptrue = "true"
  let string_of_predicate p = p

  type statement = string
    
  let void_stmt = "void"
  let append_stmt s1 s2 = s1 ^ "; " ^ s2
  let assert_stmt p = "assert " ^ p
  let string_of_stmt s = s

end

module Seq = Mix_cfg.Make(X)
open Seq

let report_loc lb =
  let b,e = lexeme_start_p lb, lexeme_end_p lb in
  eprintf "File \"%s\", " b.pos_fname;
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "line %d, characters %d-%d:@\n" l fc lc

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
	report_loc lb; eprintf "Lexical error: %s@." s; exit 1
    | Parsing.Parse_error -> 
	report_loc lb; eprintf "Syntax error@."; exit 1

(***
let interp_stmt = function
  | PSinvariant i -> Seq.Ainvariant i
  | PSjump l -> Seq.Ajump l
  | PScond l -> Seq.Acond (l, "cond true", "cond false")
  | PShalt -> Seq.Ahalt
  | PSother s -> Seq.Aother s

let asm = List.map (fun (l,s) -> (l, interp_stmt s)) asm
***)
let asm = []

let cl = Seq.transform asm Sys.argv.(2)

let print_seq_code fmt c = 
  begin match c.seq_pre with
    | Some p -> fprintf fmt "pre { %s }@\n" (X.string_of_predicate p)
    | None -> ()
  end;
  fprintf fmt "code %s@\n@\n" (X.string_of_stmt c.seq_code)

let () = List.iter (print_seq_code std_formatter) cl


