(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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

  open Rc

  type element =
    { name : string;
      attributes : (string * rc_value) list;
      elements : element list;
    }

  let buf = Buffer.create 17

  let rec pop_all group_stack element_stack =
    match group_stack with
      | [] -> element_stack
      | (elem,att,elems)::g ->
	  let e = {
	    name = elem;
	    attributes = att;
	    elements = List.rev element_stack;
	  }
	  in pop_all g (e::elems)
}

let space = [' ' '\t' '\r' '\n']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ident = (letter | digit | '_') + 
let sign = '-' | '+' 
let integer = sign? digit+
let mantissa = ['e''E'] sign? digit+
let real = sign? digit* '.' digit* mantissa?
let escape = ['\\''"''n''t''r'] 

rule elements group_stack element_stack = parse
  | space+ 
      { elements group_stack element_stack lexbuf }
  | '<' (ident as elem)   
      { attributes group_stack element_stack elem [] lexbuf }
  | "</" (ident as celem) space* '>'
      { match group_stack with
         | [] -> 
             Format.eprintf "Xml: warning unexpected closing Xml element `%s'@." celem;
             elements group_stack element_stack lexbuf
         | (elem,att,stack)::g ->
             if celem <> elem then
               Format.eprintf "Xml: warning Xml element `%s' closed by `%s'@." elem celem;
	     let e = {
	        name = elem;
	        attributes = att;
	        elements = List.rev element_stack;
	     }
             in elements g (e::stack) lexbuf            
       }
  | '<'
      { Format.eprintf "Xml: warning unexpected '<'@.";
        elements group_stack element_stack lexbuf }      
  | eof 
      { match group_stack with
         | [] -> element_stack
         | (elem,_,_)::_ ->
             Format.eprintf "Xml: warning unclosed Xml element `%s'@." elem;
             pop_all group_stack element_stack
      }
  | _ as c
      { failwith ("Xml: invalid element starting with " ^ String.make 1 c) }

and attributes groupe_stack element_stack elem acc = parse
  | space+
      { attributes groupe_stack element_stack elem acc lexbuf }
  | (ident as key) space* '=' 
      { let v = value lexbuf in
        attributes groupe_stack element_stack elem ((key,v)::acc) lexbuf }
  | '>' 
      { elements ((elem,acc,element_stack)::groupe_stack) [] lexbuf }
  | "/>"
      { let e = { name = elem ; 
                  attributes = acc;
                  elements = [] }
        in
        elements groupe_stack (e::element_stack) lexbuf }
  | _ as c
      { failwith ("Xml: `>' expected, got " ^ String.make 1 c) }
  | eof
      { failwith ("Xml: unclosed element, `>' expected") }

and value = parse
  | space+ 
      { value lexbuf }
  | integer as i
      { RCint (int_of_string i) }
  | real as r
      { RCfloat (float_of_string r) }
  | '"' 
      { Buffer.clear buf;
	string_val lexbuf } 
  | "true"
      { RCbool true }
  | "false"
      { RCbool false }
  | ident as id
      { RCident id }
  | _ as c
      { failwith ("Xml: invalid value starting with " ^ String.make 1 c) }
  | eof
      { failwith "Xml: unterminated keyval pair" }

and string_val = parse 
  | '"' 
      { RCstring (Buffer.contents buf) }
  | [^ '\\' '"'] as c
      { Buffer.add_char buf c;
        string_val lexbuf }
  | '\\' (['\\''\"'] as c)   
      { Buffer.add_char buf c;
        string_val lexbuf }
  | '\\' 'n'
      { Buffer.add_char buf '\n';
        string_val lexbuf }
  | '\\' (_ as c)
      { Buffer.add_char buf '\\';
        Buffer.add_char buf c;
        string_val lexbuf }
  | eof
      { failwith "Xml: unterminated string" }


{

  let from_file f =
      let c = 
(*
	try 
*)
	open_in f 
(*
	with Sys_error _ -> 
	  Format.eprintf "Cannot open file %s@." f;
	  exit 1
*)
      in
      let lb = from_channel c in
      let l = elements [] [] lb in
      close_in c;
      List.rev l

}
