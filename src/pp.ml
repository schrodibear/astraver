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



(*s Pretty-print library *)

open Format

let print_option f fmt = function
  | None -> ()
  | Some x -> f fmt x

let print_option_or_default default f fmt = function
  | None -> fprintf fmt "%s" default
  | Some x -> f fmt x

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let print_list_or_default default sep print fmt = function
  | [] -> fprintf fmt "%s" default
  | l -> print_list sep print fmt l

let print_list_par sep pr fmt l =
  print_list sep (fun fmt x -> fprintf fmt "(%a)" pr x) fmt l

let print_iter1 iter sep print fmt l =
  let first = ref true in
  iter (fun x -> 
          if !first
          then first := false
          else sep fmt (); 
          print fmt x ) l

let print_iter2 iter sep1 sep2 print1 print2 fmt l =
  let first = ref true in
  iter (fun x y -> 
          if !first
          then first := false
          else sep1 fmt (); 
          print1 fmt x;sep2 fmt (); print2 fmt y) l


let print_list_delim start stop sep pr fmt = function
  | [] -> ()
  | l -> fprintf fmt "%a%a%a" start () (print_list sep pr) l stop ()

let print_pair_delim start sep stop pr1 pr2 fmt (a,b) =
  fprintf fmt "%a%a%a%a%a" start () pr1 a sep () pr2 b stop ()

let comma fmt () = fprintf fmt ",@ "
let simple_comma fmt () = fprintf fmt ", "
let underscore fmt () = fprintf fmt "_"
let semi fmt () = fprintf fmt ";@ "
let space fmt () = fprintf fmt " "
let alt fmt () = fprintf fmt "|@ "
let newline fmt () = fprintf fmt "@\n"
let arrow fmt () = fprintf fmt "@ -> "
let lbrace fmt () = fprintf fmt "{"
let rbrace fmt () = fprintf fmt "}"
let lsquare fmt () = fprintf fmt "["
let rsquare fmt () = fprintf fmt "]"
let lparen fmt () = fprintf fmt "("
let rparen fmt () = fprintf fmt ")"
let lchevron fmt () = fprintf fmt "<"
let rchevron fmt () = fprintf fmt ">"
let nothing _fmt _ = ()
let string fmt s = fprintf fmt "%s" s
let int fmt i = fprintf fmt "%d" i
let constant_string s fmt () = string fmt s

let print_pair pr1 = print_pair_delim lparen comma rparen pr1

let hov n fmt f x = pp_open_hovbox fmt n; f x; pp_close_box fmt ()

let open_formatter ?(margin=78) cout =
  let fmt = formatter_of_out_channel cout in
  pp_set_margin fmt margin;
  pp_open_box fmt 0; 
  fmt

let close_formatter fmt = 
  pp_close_box fmt ();
  pp_print_flush fmt ()

let open_file_and_formatter ?(margin=78) f =
  let cout = open_out f in
  let fmt = open_formatter ~margin cout in
  cout,fmt

let close_file_and_formatter (cout,fmt) =
  close_formatter fmt;
  close_out cout

let print_in_file_no_close ?(margin=78) p f =
  let cout,fmt = open_file_and_formatter ~margin f in
  p fmt;
  close_formatter fmt;
  cout

let print_in_file ?(margin=78) p f =
  let cout = print_in_file_no_close ~margin p f in
  close_out cout


