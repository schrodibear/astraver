open Java_ast


let parse_annot loc s f =
  let lb = Lexing.from_string s in
  lb.Lexing.lex_curr_p <- loc;
  try
    f Java_lexer.next_token lb
  with Parsing.Parse_error ->
    Java_options.parsing_error (Java_lexer.loc lb) ""

let field_decl f = 
  match f with
    | JPFmethod(m,b) -> JPFmethod(m,b) (* TODO *)
    | JPFconstructor c -> assert false (* TODO *)
    | JPFvariable _ -> f 
    | JPFstatic_initializer b -> 
	assert false (* TODO *)
	(* JPFstatic_initializer (block b) *)
    | JPFannot (loc,s) -> parse_annot loc s Java_parser.kml_field_decl
    | JPFinvariant _ 
    | JPFmethod_spec _ -> assert false

  
let class_decl c = 
  { c with class_fields = List.map field_decl c.class_fields }

let interface_decl i = assert false (* TODO *)

let type_decl d =
  match d with
    | JPTclass c -> JPTclass (class_decl c)
    | JPTinterface i -> JPTinterface (interface_decl i)
    | JPTannot(loc,s) -> parse_annot loc s Java_parser.kml_type_decl
    | JPTaxiom _ 
    | JPTlogic_type_decl _
    | JPTlogic_reads _ 
    | JPTlogic_def _ -> assert false


let compilation_unit cu =
  { cu with cu_type_decls = List.map type_decl cu.cu_type_decls }

let file f = 
  try
    let c = open_in f in
    let d = Java_lexer.parse f c in
    close_in c; 
    compilation_unit d 
  with
    | Java_lexer.Lexical_error(l,s) ->
	Format.eprintf "%a: lexical error: %s@." Loc.gen_report_position l s;
	exit 1
