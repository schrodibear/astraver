
(* code from Ocaml sources *)

{

  open Lexing

  let bol = ref 0 (* beginning of line, in chars *)
  let line = ref 1 (* current line number *)
  let file = ref ""

}

rule one_line = parse
  | '#' [' ' '\t']* (['0'-'9']+ as l) [' ' '\t']*
    ("\"" ([^ '\n' '\r' '"' (* '"' *) ]* as f) "\"")?
    [^ '\n' '\r']* ('\n' | '\r' | "\r\n")
      { line := int_of_string l;
	begin match f with Some f -> file := f | None -> () end;
	bol := lexeme_start lexbuf;
	lexeme_end lexbuf }
  | [^ '\n' '\r']*
    ('\n' | '\r' | "\r\n")
      { incr line;
        bol := lexeme_start lexbuf;
        lexeme_end lexbuf }
  | [^ '\n' '\r'] * eof
      { incr line;
        bol := lexeme_start lexbuf;
        raise End_of_file }

{

  let from_char f c =
    let cin = open_in_bin f in
    let lb = from_channel cin in
    file := f;
    line := 1;
    bol := 0;
    begin try while one_line lb <= c do () done with End_of_file -> () end;
    close_in cin;
    (!file, !line - 1, c - !bol)

}
