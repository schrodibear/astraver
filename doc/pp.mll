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

{
  open Lexing

  let color = ref false

  let in_comment = ref false
  let in_slashshash = ref false

  let why_keywords =
    let h  = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ "absurd"; "and"; "array"; "as"; "assert"; "axiom"; "begin"; "bool";
        "do"; "done"; "else"; "end"; "exception"; "exists"; "external";
        "false"; "for"; "forall"; "fun"; "function"; "goal"; "if"; "in";
        "int"; "invariant"; "let"; "logic"; "not"; "of"; "or"; "parameter";
        "predicate"; "prop"; "raise"; "raises"; "reads"; "real"; "rec"; "ref";
        "returns"; "then"; "true"; "try"; "type"; "unit"; "variant"; "void";
        "while"; "with"; "writes";
      ];
    h

  let ocaml_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"fun"; "match"; "with"; "begin";
	"end"; "try"; "as"; "let"; "rec"; "in";
	"function"; "if"; "private"; "then"; "else"; "sig"; "val";
	"type"; "module";
	"while"; "do"; "done"; "for"; "struct"; "to"; "raise"
      ];
    h

  let coq_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"Inductive"; "Fixpoint" ; "Definition" ; "Lemma" ;
	"forall" ; "exists" ; "match" ; "with" ; "end" ; "as" ;
	"if" ; "then" ; "else" ;
      ];
    h

  let c_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"break"; "case"; "continue";
	"default"; "do"; "else"; "for"; "goto"; "if";
	"return"; "switch"; "while";
	"struct" ; "typedef"; "union";
	"reads" ;
	"requires"; "invariant";
	"loop" ; "variant" ;
	"ensures" ; "assigns"; "assumes"; "behavior";
	"logic" ; "type" ; "predicate" ; "axiom"; "lemma"; "inductive";
      ];
    h

  let java_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"break"; "case"; "continue"; "new";
	"default"; "do"; "else"; "for"; "goto"; "if";
	"return"; "switch"; "while";
	"class" ; "interface" ;
	"public" ; "private" ; "static" ;
	"throws" ; "extends" ; "implements" ; "reads" ;
	"requires"; "invariant"; "ensures" ; "assigns"; "signals" ;
	"logic" ; "type" ; "predicate" ; "axiom";
	"behavior" ; "model";
      ];
    h

  let bs_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"valid"; "forall"; "exists" ; "old" ; "at" ; "fresh" ; "nothing" ; "result"; "valid_range" ; "null" ; "max"; "abs"; "cos";
      ];
    h

  let c_types =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"char"; "const"; "double"; "enum"; "extern";
	"float"; "int"; "long"; "register";
	"short"; "signed"; "static"; "struct";
	"typedef"; "union"; "unsigned"; "void"; "volatile"
      ];
    h

  let is_ocaml_keyword s = Hashtbl.mem ocaml_keywords s
  let is_coq_keyword s = Hashtbl.mem coq_keywords s
  let is_c_keyword s = Hashtbl.mem c_keywords s
  let is_c_keytype s = Hashtbl.mem c_types s
  let is_java_keyword s = Hashtbl.mem java_keywords s
  let is_bs_keyword s = Hashtbl.mem bs_keywords s
  let is_why_keyword s = Hashtbl.mem why_keywords s

  let print_ident =
    let print_ident_char c =
      if c = '_' then print_string "\\_{}" else print_char c
    in
    String.iter print_ident_char

  let begin_tt () =
    print_string "\\begin{flushleft}\\ttfamily\\upshape\n";
    print_string "%BEGIN LATEX\n";
    print_string "\\parindent 0pt\n";
    print_string "%END LATEX\n"

  let end_tt () = print_string "\\end{flushleft}"

}

let space = [' ' '\t']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let beamerspec = ['0'-'9' '-' ',']+
let beameraction = "uncover" | "visible" | "invisible" | "only" | "onslide"

rule ktt = parse
  | '{'  { print_string "\\{"; ktt lexbuf }
  | '}'  { print_string "\\}"; ktt lexbuf }
  | '#'  { print_string "\\diese{}"; ktt lexbuf }
  | '_'  { print_string "\\_{}"; ktt lexbuf }
  | '&'  { print_string "\\&{}"; ktt lexbuf }
  | '%'  { print_string "\\%{}"; ktt lexbuf }
  | '\n' { if !in_slashshash then begin
	     print_string "\\end{slshape}";
	     in_slashshash := false ; in_comment := false
	   end;
	   print_string "~\\\\\n"; ktt lexbuf }
(*
  | ">=" { print_string "\\ensuremath{\\geq}"; ktt lexbuf }
  | "<=" { print_string "\\ensuremath{\\leq}"; ktt lexbuf }
  | ">" { print_string "\\ensuremath{>}"; ktt lexbuf }
  | "<" { print_string "\\ensuremath{<}"; ktt lexbuf }
  | "<>" { print_string "\\ensuremath{\\neq}"; ktt lexbuf }
  | "==" { print_string "\\ensuremath{=}"; ktt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; ktt lexbuf }
  | "==>" { print_string "\\ensuremath{\\Rightarrow}"; ktt lexbuf }
  | "<==>" { print_string "\\ensuremath{\\Leftrightarrow}"; ktt lexbuf }
*)
  | "\\end{krakatoa}" { () }
  | "\\emph{" [^'}''\n']* '}' { print_string (lexeme lexbuf); ktt lexbuf }
  | "\\" beameraction "<" beamerspec ">"
      { print_string (lexeme lexbuf); ktt lexbuf
      }
  | "/*@"
      { print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
        print_string "/*@";
	ktt lexbuf }
  | "/*"
      { print_string "\\begin{slshape}\\rmfamily\\color{darkgreen}/*";
	in_comment := true;
	ktt lexbuf }
  | "*/" { print_string "*/\\end{slshape}";
	   in_comment := false;
	   ktt lexbuf }
  | "//@"
      { in_slashshash := true;
	print_string "\\begin{slshape}\\color{blue}//@";
	ktt lexbuf }
  | "//"
      { in_comment := true;
	in_slashshash := true;
	print_string "//\\begin{slshape}\\rmfamily\\color{darkgreen}";
	ktt lexbuf }
  | eof  { () }
  | '-'  { print_string "$-$"; ktt lexbuf }
  | "'a" { print_string "\\ensuremath{\\alpha}"; ktt lexbuf }
  | "::" { print_string ":\\hspace*{-0.1em}:"; ktt lexbuf }
  | " "  { print_string "~"; ktt lexbuf }
  | "\t"  { print_string "~~~~~~~~"; ktt lexbuf }
  | "[" (ident as s) "]"
      { if !in_comment then print_string "{\\ttfamily " else print_string "[";
	print_ident s;
	if !in_comment then print_string "}" else print_string "]";
	ktt lexbuf
      }
  | ident as s
	{ if not !in_comment && is_java_keyword s then
	      begin
		print_string "\\textbf{"; print_ident s;
		print_string "}"
	      end
	  else
              print_ident s;
	  ktt lexbuf
	}
  | "\\" (ident as s)
      { if not !in_comment && is_bs_keyword s then
	    begin
	      print_string "\\textbf{\\char'134 "; print_ident s;
	      print_string "}"
	    end
	else
            print_string (lexeme lexbuf);
	ktt lexbuf
      }
  | _
      { print_string (lexeme lexbuf); ktt lexbuf }


and ctt = parse
  | '{'  { print_string "\\{"; ctt lexbuf }
  | '}'  { print_string "\\}"; ctt lexbuf }
  | '#'  { print_string "\\verb|#|"; ctt lexbuf }
  | '_'  { print_string "\\_{}"; ctt lexbuf }
  | '&'  { print_string "\\&{}"; ctt lexbuf }
  | '%'  { print_string "\\%{}"; ctt lexbuf }
  | '\n' { if !in_slashshash then begin
	     print_string "\\end{slshape}";
	     in_slashshash := false ; in_comment := false
	   end;
	   print_string "~\\\\\n"; ctt lexbuf }
(*
  | ">=" { print_string "\\ensuremath{\\geq}"; ctt lexbuf }
  | "<=" { print_string "\\ensuremath{\\leq}"; ctt lexbuf }
  | ">" { print_string "\\ensuremath{>}"; ctt lexbuf }
  | "<" { print_string "\\ensuremath{<}"; ctt lexbuf }
  | "<>" { print_string "\\ensuremath{\\neq}"; ctt lexbuf }
  | "==" { print_string "\\ensuremath{=}"; ctt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; ctt lexbuf }
  | "==>" { print_string "\\ensuremath{\\Rightarrow}"; ctt lexbuf }
  | "<==>" { print_string "\\ensuremath{\\Leftrightarrow}"; ctt lexbuf }
*)
  | "\\end{c}" { () }
  | "\\emph{" [^'}''\n']* '}' { print_string (lexeme lexbuf); ctt lexbuf }
  | "\\" beameraction "<" beamerspec ">"
      { print_string (lexeme lexbuf); ctt lexbuf
      }
  | "/*@"
      { print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "/*@";
	ctt lexbuf }
  | "/*"
      { print_string "\\begin{slshape}\\rmfamily\\color{darkgreen}/*";
	in_comment := true;
	ctt lexbuf }
  | "*/" { print_string "*/\\end{slshape}";
	   in_comment := false;
	   ctt lexbuf }
  | "//@"
      { in_slashshash := true;
	print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "//@";
	ctt lexbuf }
  | "//"
      { in_comment := true;
	if !in_slashshash then
	  print_string "\\rmfamily\\color{darkgreen}//"
	else
	  print_string "\\begin{slshape}\\rmfamily\\color{darkgreen}//";
        in_slashshash := true;
	ctt lexbuf }
  | eof  { () }
  | '-'  { print_string "$-$"; ctt lexbuf }
  | "::" { print_string ":\\hspace*{-0.1em}:"; ctt lexbuf }
  | " "  { print_string "~"; ctt lexbuf }
  | "\t"  { print_string "~~~~~~~~"; ctt lexbuf } (* tab is 8 spaces *)
  | "[" (ident as s) "]"
      { if !in_comment then print_string "{\\ttfamily " else print_string "[";
	print_ident s;
	if !in_comment then print_string "}" else print_string "]";
	ctt lexbuf
      }
  | ident as s
	{ if not !in_comment && is_c_keyword s then
	      begin
		print_string "\\textbf{"; print_ident s;
		print_string "}"
	      end
	  else (* if is_c_keytype s then begin
		  print_string "{\\color{black}"; print_string s;
		  print_string "}"
		  end else *)
              print_ident s;
	  ctt lexbuf
	}
  | "\\" (ident as s)
      { if not !in_comment && is_bs_keyword s then
	    begin
	      print_string "\\textbf{\\char'134 "; print_ident s;
	      print_string "}"
	    end
	else
          print_string (lexeme lexbuf);
	ctt lexbuf
      }
  | _
      { print_string (lexeme lexbuf); ctt lexbuf }


and coqtt = parse
  | "\\end{coq}" { () }
  | '{'  { print_string "\\{"; coqtt lexbuf }
  | '}'  { print_string "\\}"; coqtt lexbuf }
  | '\n' { print_string "~\\\\\n"; coqtt lexbuf }
  | ">=" { print_string "\\ensuremath{\\geq}"; coqtt lexbuf }
  | "<=" { print_string "\\ensuremath{\\leq}"; coqtt lexbuf }
  | ">" { print_string "\\ensuremath{>}"; coqtt lexbuf }
  | "<" { print_string "\\ensuremath{<}"; coqtt lexbuf }
  | "<>" { print_string "\\ensuremath{\\neq}"; coqtt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; coqtt lexbuf }
  | "forall" { print_string "\\ensuremath{\\forall}"; coqtt lexbuf }
  | "exists" { print_string "\\ensuremath{\\exists}"; coqtt lexbuf }
  | "/\\" { print_string "\\ensuremath{\\land}"; coqtt lexbuf }
  | "\\/" { print_string "\\ensuremath{\\lor}"; coqtt lexbuf }
  | '_'  { print_string "\\_{}"; coqtt lexbuf }
  | '|'  { print_string "\\textbf{|}"; coqtt lexbuf }
  | "=>"  { print_string "\\ensuremath{\\Rightarrow}"; coqtt lexbuf }
  | "Z"  { print_string "\\ensuremath{\\mathbb{Z}}"; coqtt lexbuf }
  | "\\" beameraction "<" beamerspec ">"
      { print_string (lexeme lexbuf); coqtt lexbuf
      }
  | "(*"
      { print_string "\\begin{slshape}\\color{darkgreen}(*";
	in_comment := true;
	coqtt lexbuf }
  | "*)" { print_string "*)\\end{slshape}";
	   in_comment := false;
	   coqtt lexbuf }
  | eof  { () }
  | " "  { print_string "~"; coqtt lexbuf }
  | "[" (ident as s) "]"
      { if !in_comment then print_string "{\\ttfamily ";
	print_ident s;
	if !in_comment then print_string "}";
	coqtt lexbuf
      }
  | ident as s
      { if not !in_comment && is_coq_keyword s then
	    begin
	      print_string "\\textbf{"; print_ident s;
	      print_string "}"
	    end
	else
            print_ident s;
	coqtt lexbuf
      }
  | _   { print_string (lexeme lexbuf); coqtt lexbuf }

and whytt = parse
  | '{'  { print_string "\\{"; whytt lexbuf }
  | '}'  { print_string "\\}"; whytt lexbuf }
(*
  | '\\' { print_string "\\ensuremath{\\backslash}"; whytt lexbuf }
*)
  | '#' { print_string "\\diese{}"; whytt lexbuf }
  | '_'  { print_string "\\_{}"; whytt lexbuf }
  | '%'  { print_string "\\%{}"; whytt lexbuf }
  | '&'  { print_string "\\&{}"; whytt lexbuf }
  | '%'  { print_string "\\%{}"; whytt lexbuf }
  | '\n' { print_string "\\linebreak\n\\hspace*{0pt}"; whytt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; whytt lexbuf }
  | "=>" { print_string "\\ensuremath{\\Rightarrow}"; whytt lexbuf }
  | "<->" { print_string "\\ensuremath{\\leftrightarrow}"; whytt lexbuf }
  | '\n' "\\end{" "why" "}\n" { print_newline () }
  | "\\emph{" [^'}']* '}' { print_string (lexeme lexbuf); whytt lexbuf }
  | eof  { () }
  | "'a" { print_string "\\ensuremath{\\alpha}"; whytt lexbuf }
  | "'t" { print_string "\\ensuremath{\\tau}"; whytt lexbuf }
  | "*"  { print_string "\\ensuremath{\\times}"; whytt lexbuf }
  | "."  { print_string "\\ensuremath{.\\!\\!}"; whytt lexbuf }
  | ":"  { print_string "\\ensuremath{:}"; whytt lexbuf }
  | "forall" { print_string "\\ensuremath{\\forall\\!\\!\\!}"; whytt lexbuf }
  | ident as s
	{ if is_why_keyword s then
	      begin
		print_string "\\textbf{"; print_ident s;
		print_string "}"
	      end
	  else print_ident s;
	  whytt lexbuf
	}
  | _   { print_string (lexeme lexbuf); whytt lexbuf }

and pp = parse
  | "\\begin{krakatoa}" space* "\n"
      { begin_tt();
	ktt lexbuf;
	end_tt();
	pp lexbuf }
  | "\\begin{coq}" space* "\n"
      { begin_tt();
	coqtt lexbuf;
	end_tt();
	pp lexbuf }
  | "�" { print_string "\\'e"; pp lexbuf }
  | "�" { print_string "\\`e"; pp lexbuf }
  | "�" { print_string "\\`a"; pp lexbuf }
  | "�" { print_string "\\^a"; pp lexbuf }
  | "�" { print_string "\\^e"; pp lexbuf }
  | "�" { print_string "\\^{\\i}"; pp lexbuf }
  | "�" { print_string "\\\"{\\i}"; pp lexbuf }
  | "�" { print_string "\\^u"; pp lexbuf }
  | "�" { print_string "\\`u"; pp lexbuf }
  | "�" { print_string "\\\"o"; pp lexbuf }
  | "�" { print_string "\\^o"; pp lexbuf }
  | eof
      { () }
  | _
      { print_string (lexeme lexbuf); pp lexbuf }

{


  let tex_files = ref []
  let c_files = ref []
  let java_files = ref []
  let why_files = ref []

  let () = Arg.parse
    [
      "-color", Arg.Set color, "print in color" ;
      "-c", Arg.String (fun f ->
			      c_files := f :: !c_files), "read C file <f>" ;
      "-java", Arg.String (fun f ->
			      java_files := f :: !java_files), "read Java file <f>" ;
      "-why", Arg.String (fun f ->
			      why_files := f :: !why_files), "read Why file <f>" ;
    ]
    (fun f -> tex_files := f :: !tex_files)
    "pp [options] file..."


  let () =
    List.iter
      (fun (l,func) ->
	 List.iter
	   (fun f ->
	      let cin = open_in f in
	      let lb = from_channel cin in
	      func lb;
	      close_in cin)
	   l)
      [!tex_files, pp;
       !why_files, (fun lb -> begin_tt (); whytt lb; end_tt ());
       !c_files, (fun lb -> begin_tt (); ctt lb; end_tt ());
       !java_files, (fun lb -> begin_tt (); ktt lb; end_tt ()) ]


}
