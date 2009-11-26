(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: encoding.ml,v 1.12 2009-11-26 16:07:03 andrei Exp $ i*)

open Options

let queue = Queue.create ()

let reset () = match get_types_encoding () with
  | NoEncoding -> Queue.clear queue
  | Predicates -> Encoding_pred.reset ()
  | Stratified -> Encoding_strat.reset ()
  | SortedStratified -> Encoding_mono.reset ()
  | Recursive -> Encoding_rec.reset ()
  | Monomorph -> Monomorph.reset ()

let push d = match get_types_encoding () with
  | NoEncoding -> Queue.add d queue
  | Predicates -> Encoding_pred.push d
  | SortedStratified -> Encoding_mono.push d
  | Stratified -> Encoding_strat.push d
  | Recursive -> Encoding_rec.push d
  | Monomorph -> Monomorph.push_decl d

let push = function
  | Logic_decl.Dinductive_def (loc, id, d) ->
      List.iter push (PredDefExpansor.inductive_def loc id d)
  | Logic_decl.Dalgtype (loc, id, d) ->
      List.iter push (PredDefExpansor.algebraic_type loc id d)
  | d -> push d

let iter f = match get_types_encoding () with
  | NoEncoding -> Queue.iter f queue
  | Predicates -> Encoding_pred.iter f
  | Stratified -> Encoding_strat.iter f
  | SortedStratified -> Encoding_mono.iter f
  | Recursive -> Encoding_rec.iter f
  | Monomorph -> Monomorph.iter f

let symbol ((id,_) as s) = match get_types_encoding () with
  | Monomorph -> Monomorph.symbol s
  | _ -> Ident.string id
