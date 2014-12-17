
(* préprocesseur pour les environnement ocaml (sans alltt) *)

{
  open Lexing 

  let slides = ref true

  let c_keywords = 
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ "if"; "for"; "return";
	"type"; "predicate"; "axiom"; "logic";
	"variant"; "invariant"; "requires"; "ensures"; "assigns";
	"loop_assigns"; "label"; "assert";
      ];
    h

  let is_keyword s = Hashtbl.mem c_keywords s 

  let print_ident =
    let print_ident_char c = 
      if c = '_' then print_string "\\_{}" else print_char c
    in
    String.iter print_ident_char

  let slashslash_line = ref false

}

let space = [' ' '\t']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule alltt = parse
  | '{'  { print_string "\\{"; alltt lexbuf }
  | '}'  { print_string "\\}"; alltt lexbuf }
  | '#' { print_string "\\diese{}"; alltt lexbuf }
  | '_'  { print_string "\\_{}"; alltt lexbuf }
  | '%'  { print_string "\\%{}"; alltt lexbuf }
  | '&'  { print_string "\\&{}"; alltt lexbuf }
  | '%'  { print_string "\\%{}"; alltt lexbuf }
  | '~'  { print_string "\\~{}"; alltt lexbuf }
  | '\\' { print_string "\\ensuremath{\\backslash}"; alltt lexbuf }
  | '\n' { if !slashslash_line then begin
	     print_string "\\end{minipage}}"; slashslash_line := false
	   end;
	   print_string "\\linebreak\n\\hspace*{0pt}"; alltt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; alltt lexbuf }
  | "=>" { print_string "\\ensuremath{\\Rightarrow}"; alltt lexbuf }
  | "<=>" { print_string "\\ensuremath{\\Leftrightarrow}"; alltt lexbuf }
  | "<->" { print_string "\\ensuremath{\\leftrightarrow}"; alltt lexbuf }
  | "<" { print_string "\\ensuremath{<}"; alltt lexbuf }
  | "<=" { print_string "\\ensuremath{\\le}"; alltt lexbuf }
  | '\n' space* "\\end{caduceus}" space* "\n" 
      { if !slashslash_line then begin
	     print_string "\\end{minipage}}"; slashslash_line := false
	end;
	print_newline () }
  | "\\emph{" [^'}''\n']* '}' { print_string (lexeme lexbuf); alltt lexbuf }
  | eof  { () }
  | "'a" { print_string "\\ensuremath{\\alpha}"; alltt lexbuf }
  | "::" { print_string ":\\hspace*{-0.1em}:"; alltt lexbuf }
  | " "  { print_string "~"; alltt lexbuf }
  | ident as s
	{ if !slides && is_keyword s then begin
	    print_string "{\\color{blue}"; 
	    print_string (if s = "loop_assigns" then "loop\\_assigns" else s);
	    print_string "}"
	  end else 
            print_ident s;
	  alltt lexbuf 
	}
  | (space* as s) "/*" 
        { print_string "\\colorbox{red!10}{\\begin{minipage}{\\textwidth}\\slshape{}\\color{red}"; 
	  String.iter (fun _ -> print_string "~") s; print_string "/*";
	  alltt lexbuf }
  | (space* as s) "//" 
        { slashslash_line := true;
	  print_string "\\colorbox{red!10}{\\begin{minipage}{\\textwidth}\\slshape{}\\color{red}"; 
	  String.iter (fun _ -> print_string "~") s; print_string "//";
	  alltt lexbuf }
  | "*/"
        { print_string "*/\\end{minipage}}"; alltt lexbuf }
  | _   { print_string (lexeme lexbuf); alltt lexbuf }

and pp = parse
  | "\\begin{caduceus}" space* "\n" 
      { print_string "\n\n\\medskip{\\tt\\parindent 0pt\n"; 
	alltt lexbuf;
	print_string "\n}\n\n\\medskip\n";
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
  let f = Sys.argv.(1)
  (*let () = slides := (String.length f > 6 && String.sub f 0 7 = "slides-")*)
  let cin = open_in f
  let lb = from_channel cin
  let _ = pp lb
}
