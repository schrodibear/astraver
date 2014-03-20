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

open Mlpost
open Num
open Box

let tabular l =
  "{\\begin{tabular}{l} \\sf " ^ String.concat " \\\\ \\sf " l ^ "\\end{tabular}}"

let dx = bp 5. and dy = bp 5.

let space ~name b = rect ~stroke:None ~name ~dx ~dy b

let color_tool_default = Color.color "light pink"

let color_why3_tool = color_tool_default (* Color.color "light pink" *)

let color_frama_c = Color.rgb8 255 128 255

let color_why3_box = Color.color "light cyan"

let color_why2_box = Color.color "light yellow"

let tool ?(color=color_tool_default) ?name  s =
    space ~name:(match name with None -> s | Some s -> s)
      (shadow (rect  ~dx ~dy ~fill:color
                              (tex ("\\large\\sf " ^ s))))

let green ?(color=Color.lightgreen) n s =
  space ~name:n
    (round_rect ~dx ~dy ~stroke:None ~fill:color (tex (tabular s)))

let why_platform n =
  let emptyn x y = if x=n then y else empty () in
  let interactive = tex ~name:"interactive"
    (tabular ["Interactive provers";
              "(Coq, PVS,";
              "Isabelle/HOL, etc.)"]) in
  let automatic = tex ~name:"automatic"
    (tabular ["Automatic provers";
	      "(Alt-Ergo, CVC3, Gappa,";
              "Simplify, veriT, Yices,";
              "Z3, etc.)"]) in
  let tptp = tex ~name:"TPTP"
    (tabular ["More automatic provers";
	      "(Eprover, SPASS, ";
              "Vampire, etc.)"]) in
  let b =
    tabularl ~hpadding:(bp 20.) ~vpadding:(bp 15.)
      [[ green "JMLJava" ["KML-annotated" ;"Java program"] ; empty ();
	 green "ACSLC" ["ACSL-annotated"; "C program"]; empty () ] ;
       [ tool "Krakatoa" ; empty (); tool ~color:color_frama_c "Frama-C";
         empty () ];
       [ empty ();  tool "Jessie" ; empty (); empty ()];
       [ empty () ; tool ~name:"VCG" "VC generator" ;
         emptyn 2 (tool ~color:color_why3_tool ~name:"VCG3" "VC generator");
         green "Theories" ["Theories"]];
       [ empty () ; green "VC" ["verification";"conditions"];
         emptyn 2 (green "VC3" ["verification";"conditions"]) ;
         tool ~color:color_why3_tool ~name:"Tr" "Transformations"];
       [ tex "\\LARGE\\sf Why 2.30" ; tool ~name:"Enc" "Encodings" ;
         emptyn 2 (tool ~color:color_why3_tool ~name:"Enc3" "Encodings") ;
         tex "\\LARGE\\sf Why3 0.71" ];
       [ empty (); tex "~"; empty ();empty ()] ;
       [ empty (); tex "~"; empty ();empty ()] ;
       [ empty (); interactive; automatic;tptp]
]
  in
  let why = round_rect ~fill:color_why2_box ~dx:(bp 114.0) ~dy:(bp 140.0)
    (tex "")
  in
  let why = shift (Point.pt (bp 114.0, bp (-.170.0))) why in
  let why3 = round_rect ~fill:color_why3_box ~dx:(bp 140.0) ~dy:(bp 90.0)
    (tex "")
  in
  let why3 = shift (Point.pt (bp 390.0, bp (-.215.0))) why3 in
  let arrow ?(shifty=0.0) x y =
    let s b = shift (Point.pt (bp 0.0, bp shifty)) b in
    let p = Box.cpath (s (get x b)) (s (get y b)) in
    Arrow.draw_thick ~line_color:Color.red ~width:(bp 4.) ~head_width:(bp 10.)
      ~fill_color:Color.red (Path.point 0. p) (Path.point 1. p)
  in
  let arrown ?shifty x y z =
    if x=n then arrow ?shifty y z else Command.nop
  in
  Command.seq
    [ Box.draw why;
      Box.draw why3;
      Box.draw b;
      arrow "ACSLC" "Frama-C";
      arrow "Frama-C" "Jessie";
      arrow "JMLJava" "Krakatoa";
      arrow "Krakatoa" "Jessie";
      arrow "Jessie" "VCG";
      arrow "VCG" "VC";
      arrow "VC" "Enc";
      arrow "Enc" "interactive";
      arrow "Enc" "automatic";

      arrown 2 "Jessie" "VCG3";
      arrown 2 "VCG3" "VC3";
      arrown 2 "VC3" "Enc3";
      arrown ~shifty:10.0 2 "VC3" "Tr";
      arrown ~shifty:(-10.0) 2 "Tr" "VC3";
      arrown 2 "Enc3" "interactive";
      arrown 2 "Enc3" "automatic";
      arrown 2 "Enc3" "TPTP";
      arrown 2 "Theories" "VC3";
    ]

let () = Metapost.emit "why_frama_c1" (why_platform 1)
let () = Metapost.emit "why_frama_c2" (why_platform 2)


