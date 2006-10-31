
open Jc_env
open Jc_ast
open Format

let parse_file f = 
  try
    let c = open_in f in
    let d = Jc_lexer.parse f c in
    close_in c; d
  with
    | Jc_lexer.Syntax_error l ->
	eprintf "%a: syntax error@." Loc.gen_report_position l;
	exit 1
    | Jc_lexer.Lexical_error(l,s) ->
	eprintf "%a: lexical error: %s@." Loc.gen_report_position l s;
	exit 1


let main () =
  let files = Jc_options.files () in
  match files with
    | [f] ->
	let ast = parse_file f in
	List.iter Jc_typing.decl ast;
	let d = 
	  Hashtbl.fold 
	    (fun id (f,b) acc ->
	       Jc_interp.tr_fun f b acc)
	    Jc_typing.functions_table
	    []
	in	       
	let f = Filename.chop_extension f in
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls [])
	  (Lib.file "why" (f ^ "_spec.why"));
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls d)
	  (Lib.file "why" (f ^ ".why"));
	Jc_make.makefile f
    | _ -> Jc_options.usage ()
    


let _ = Printexc.catch main ()

  
