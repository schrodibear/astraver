(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

{
  open Lexing 
   
  let color = ref false

  let in_comment = ref false
  let in_slashshash = ref false

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
	"ensures" ; "assigns"; 
	"logic" ; "type" ; "predicate" ; "axiom";
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
	"valid"; "forall"; "exists" ; "old" ; "fresh" ; "nothing" ; "result"
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

  let print_ident =
    let print_ident_char c = 
      if c = '_' then print_string "\\_{}" else print_char c
    in
    String.iter print_ident_char

  let begin_tt () =
    print_string "\\begin{flushleft}\\ttfamily\\upshape\\parindent 0pt\n"

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
      { print_string "\\begin{slshape}\\color{blue}/*@"; 
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
  | "é" { print_string "\\'e"; pp lexbuf }
  | "è" { print_string "\\`e"; pp lexbuf }
  | "à" { print_string "\\`a"; pp lexbuf }
  | "â" { print_string "\\^a"; pp lexbuf }
  | "ê" { print_string "\\^e"; pp lexbuf }
  | "î" { print_string "\\^{\\i}"; pp lexbuf }
  | "ï" { print_string "\\\"{\\i}"; pp lexbuf }
  | "û" { print_string "\\^u"; pp lexbuf }
  | "ù" { print_string "\\`u"; pp lexbuf }
  | "ö" { print_string "\\\"o"; pp lexbuf }
  | "ô" { print_string "\\^o"; pp lexbuf }
  | eof 
      { () }
  | _ 
      { print_string (lexeme lexbuf); pp lexbuf }

{

  let tex_files = ref []
  let c_files = ref []
  let java_files = ref []

  let () = Arg.parse
    [
      "-color", Arg.Set color, "print in color" ;
      "-c", Arg.String (fun f ->
			      c_files := f :: !c_files), "read C file <f>" ;
      "-java", Arg.String (fun f ->
			      java_files := f :: !java_files), "read Java file <f>" ;
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
       !c_files, (fun lb -> begin_tt (); ctt lb; end_tt ());
       !java_files, (fun lb -> begin_tt (); ktt lb; end_tt ()) ]


}
