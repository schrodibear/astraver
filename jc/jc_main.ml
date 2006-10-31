
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
  if files = [] then Jc_options.usage ();
  let ast = 
     List.fold_right
       (fun f acc -> (parse_file f)@acc)
       files []
  in
  let d = Jc_interp.decls ast in
  Pp.print_in_file 
    (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls d)
    "jc/jessie.why"


let _ = Printexc.catch main ()

  
