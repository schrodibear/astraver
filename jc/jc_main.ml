
open Jc_env
open Jc_ast
open Format

let parse_file f = 
  try
    let c = open_in f in
    let d = Jc_lexer.parse f c in
    close_in c; d
  with
    | Jc_lexer.Lexical_error(l,s) ->
	eprintf "%a: lexical error: %s@." Loc.gen_report_position l s;
	exit 1


let main () =
  let files = Jc_options.files () in
  try
    match files with
    | [f] ->
	let ast = parse_file f in
	List.iter Jc_typing.decl ast;
	let d_memories =
	  Hashtbl.fold 
	    (fun id fl acc ->
	       Jc_interp.tr_struct id fl acc)
	    Jc_typing.structs_table
	    []
	in	       	  
	let d_funs = 
	  Hashtbl.fold 
	    (fun _ (f,s,b) acc ->
	       Jc_interp.tr_fun f s b acc)
	    Jc_typing.functions_table
	    d_memories
	in	       
	let f = Filename.chop_extension f in
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls d_funs)
	  (Lib.file "why" (f ^ ".why"));
	Jc_make.makefile f


    | _ -> Jc_options.usage ()
    
  with
    | Jc_typing.Typing_error(l,s) ->
	eprintf "%a: typing error: %s@." Loc.gen_report_position l s;
	exit 1
    | Jc_options.Jc_error(l,s) ->
	eprintf "%a: %s@." Loc.gen_report_position l s;
	exit 1


let _ = Printexc.catch main ()

  
