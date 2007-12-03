(* One module to rule them all, one module to find them, one module to bring
them all and in the bytecode bind them. *)

open Ml_misc
open Unix

let parse f file_name =
  (* Open file *)
  let fd = try
    openfile file_name [ O_RDONLY ] 0o640
  with
    | Unix_error _ -> error "Could not read file: %s" file_name
  in
  let chan = in_channel_of_descr fd in

  (* Parse file *)
  let lexbuf = Lexing.from_channel chan in
  Ml_ocaml.Location.init lexbuf file_name;
  try
    f Ml_ocaml.Lexer.token lexbuf
  with
    | Ml_ocaml.Lexer.Error(error, loc) ->
	caml_error loc Ml_ocaml.Lexer.report_error error
    | Parsing.Parse_error ->
	locate_error (Ml_ocaml.Location.curr lexbuf) "Parse error"

let file env (file_kind, file_name) =
  match file_kind with
    | Ml_options.Ml ->
	log "Implementation %s" file_name;
	let parse_tree = parse Ml_ocaml.Parser.implementation file_name in
	
        (* Type with the OCaml typer *)
	let typed_tree, _, new_env = try
	  Ml_ocaml.Typemod.type_structure env parse_tree
	with
	  | Ml_ocaml.Typecore.Error(loc, error) ->
	      caml_error loc Ml_ocaml.Typecore.report_error error
	in
  
        (* Interpret to a Jessie typed AST *)
        let jessie_ast, _ = Ml_interp.structure Ml_env.empty typed_tree in

        (* Open the output file *)
	log "Output file: %s" Ml_options.output_file;
	let fd = try
	  openfile Ml_options.output_file [ O_WRONLY; O_CREAT; O_TRUNC ] 0o640
	with
	  | Unix_error _ -> error "Could not open or create file: %s" file_name
	in
	let chan = out_channel_of_descr fd in

        (* Output our translation *)
	Jc_output.print_decls (Format.formatter_of_out_channel chan) jessie_ast;

	(* Return the new environment *)
	new_env
    | Ml_options.Mli ->
	log "Interface %s" file_name;
	let parse_tree = parse Ml_ocaml.Parser.interface file_name in

	(* Type with the OCaml typer *)
	let typed_tree = try
	  Ml_ocaml.Typemod.transl_signature env parse_tree
	with
	  | Ml_ocaml.Typetexp.Error(loc, error) ->
	      caml_error loc Ml_ocaml.Typetexp.report_error error
	in

	(* Return the new environment *)
	Ml_ocaml.Env.add_signature typed_tree env

let _ = List.fold_left file Ml_pervasives.default_env Ml_options.input_files

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
