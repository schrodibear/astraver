(* oct_anal.ml
   Main functions for the example analyzer.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
*)

open Oct_anal_syn;;
open Oct_anal_lex;;
open Oct_anal_yacc;;
open Oct_anal_core;;

do_debug:=true;;
widen_thres:=5;;

module Anal = Analyze(Oct);;
(* module Anal = Analyze(PolyOct);; *)


(* main *)
(* **** *)

Anal.init();;

let graph_out = open_out "result.gdl";;
let text_out = stdout;;
let html_out = open_out "result.html";;
let debug_out = open_out "result.debug";;

let progtext = Anal.stream_to_string stdin;;
let progtree = Anal.string_to_concrete text_out html_out progtext;;

let text_out = open_out "result.txt";;

let analyze_prog (name,parsetree) =
  let (v,var,n) = Anal.get_varlist parsetree in
  let graph = Anal.concrete_to_graph parsetree (v,n) in
  Anal.print_ctrlpoints debug_out progtext name graph false;
  Anal.analyze_graph debug_out var graph;
  Anal.print_graph graph_out name var graph;
  Anal.print_ctrlpoints stdout progtext name graph true;
  Anal.print_ctrlpoints text_out progtext name graph false;
  Anal.print_result text_out name var graph false;
  Anal.print_html_ctrlpoints html_out progtext name graph;
  Anal.print_html_result html_out name var graph;;

Anal.print_graph_header graph_out;;
Anal.print_html_header html_out;;
List.iter analyze_prog progtree;;
Anal.print_graph_footer graph_out;;
Anal.print_html_footer html_out;;

Anal.quit ();;
