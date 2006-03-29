(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

{

  open Lexing

  exception Lexical_error of string
  exception Eof 

  let config_file = 
    let home = 
      try Sys.getenv "HOME"
      with Not_found -> ""
    in (Filename.concat home ".gwhyrc")

  let key = Buffer.create 128
  let string_buffer = Buffer.create 128
  let config = Hashtbl.create 13

  let create_default_config () = 
    if not (Sys.file_exists config_file) then begin
      let out_channel = open_out config_file in
      output_string out_channel "prover = \"Simplify\"";
      output_string out_channel "cache = \"true\"";
      output_string out_channel "timeout = \"10\"";
      output_string out_channel "hard_proof = \"true\"";
      output_string out_channel "live_update = \"false\"";
      try close_out out_channel
      with Sys_error s -> prerr_string s
    end

  let get_values () = 
    Hashtbl.fold
      (fun k v t -> (k,v) :: t)
      config
      []

  let write_values cl = 
    let out_channel = open_out config_file in
    List.iter 
      (fun (k,v) -> output_string out_channel (k^ " = \""^ v "\""))
      cl;
    try close_out out_channel
    with Sys_error s -> prerr_string s

  let get_value key = 
    try Hashtbl.find config key 
    with Not_found -> ""

  let is_key =
    let h = Hashtbl.create 97 in
    List.iter 
      (fun s -> Hashtbl.add h s ())
      [ "prover"; "cache"; "hard_proof"; "timeout"; "live_update"];
    fun s -> 
      Hashtbl.mem h s

}

    
let space = [' ' '\010' '\013' '\009' '\012']
let char = ['A'-'Z' 'a'-'z' '_' '0'-'9']
let ident = char+

rule token = parse
  | space+        
      { token lexbuf }
  | '#' [^ '\n']* 
      { token lexbuf }
  | ident as id
      { if is_key id 
	then Buffer.add_string key id 
	else Format.eprintf ".gwhyrc : unknown key (%s)@." id }
  | '='   
      { token lexbuf }
  | '"'   
      { Buffer.reset string_buffer; 
	string lexbuf }
  | _     
      { let c = lexeme_start lexbuf in
	Format.eprintf ".gwhyrc: invalid character (%d)@." c; 
	raise Eof }
  | eof   
      { raise Eof }

and string = parse
  | '"'  
      { Hashtbl.replace config (Buffer.contents key) (Buffer.contents string_buffer);
	Buffer.reset key;
	Buffer.reset string_buffer }
  | '\\' '"' | _ 
	{ Buffer.add_string string_buffer (lexeme lexbuf); 
	  string lexbuf }
  | eof  
      { Format.eprintf ".gwhyrc: unterminated string@.";
	raise Eof}

{

  let load () = 
    try
      let in_channel = open_in config_file in
      begin
        try
          let lexbuf = Lexing.from_channel in_channel in
          while true do
            token lexbuf;
          done
        with Eof -> ()
      end;
      close_in in_channel;
    with Sys_error s ->
      begin
        print_endline ("     [...] Sys_error : "^s); flush stdout;
      end

}

