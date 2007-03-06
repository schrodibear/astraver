open Java_ast
open Format
open Lexing

let parse_annot loc s f =
  let lb = Lexing.from_string s in
(*
  eprintf "lb.pos_fname = %s@." lb.lex_curr_p.pos_fname;
  eprintf "lb.pos_lnum = %d@." lb.lex_curr_p.pos_lnum;
  eprintf "lb.pos_bol = %d@." lb.lex_curr_p.pos_bol;
  eprintf "lb.pos_cnum = %d@." lb.lex_curr_p.pos_cnum;
*)
  lb.lex_curr_p <- {loc with pos_bol = loc.pos_bol - loc.pos_cnum - 3};
(*
  eprintf "lb.pos_fname = %s@." lb.lex_curr_p.pos_fname;
  eprintf "lb.pos_lnum = %d@." lb.lex_curr_p.pos_lnum;
  eprintf "lb.pos_bol = %d@." lb.lex_curr_p.pos_bol;
  eprintf "lb.pos_cnum = %d@." lb.lex_curr_p.pos_cnum;
*)
  try
    f Java_lexer.next_token lb
  with Parsing.Parse_error ->
    Java_options.parsing_error (Java_lexer.loc lb) ""

let rec statement s =
  { s with java_pstatement_node = match s.java_pstatement_node with
    | JPSannot(loc,s) -> parse_annot loc s Java_parser.kml_statement_annot
    | JPSloop_annot _ -> assert false
    | JPSassert _ -> assert false
    | JPSsynchronized (e, s') -> JPSsynchronized(e, List.map statement s')	
    | JPSblock b -> JPSblock(List.map statement b)
    | JPSswitch(e, l) -> 
	JPSswitch(e, List.map (fun (labs,b) -> (labs,List.map statement b)) l)
    | JPStry (s, l, f) -> assert false (* TODO *)
    | JPSfor_decl (_, _, _, _) -> assert false (* TODO *)
    | JPSfor (_, _, _, _) -> assert false (* TODO *)
    | JPSdo (_, _) -> assert false (* TODO *)
    | JPSwhile (e, s') -> JPSwhile(e, statement s')
    | JPSif (e, s1, s2) -> JPSif(e, statement s1, statement s2)
    | JPSlabel (l, s') -> JPSlabel(l,statement s')
    | JPScontinue _
    | JPSbreak _
    | JPSreturn _
    | JPSthrow _
    | JPSvar_decl _
    | JPSexpr _
    | JPSskip -> s.java_pstatement_node }

let field_decl f = 
  match f with
    | JPFmethod(m,None) -> f
    | JPFmethod(m,Some b) -> JPFmethod(m,Some (List.map statement b))
    | JPFconstructor c -> assert false (* TODO *)
    | JPFvariable _ -> f 
    | JPFstatic_initializer b -> JPFstatic_initializer (List.map statement b)
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
	eprintf "%a: lexical error: %s@." Loc.gen_report_position l s;
	exit 1

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
