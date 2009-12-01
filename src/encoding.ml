(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
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

(*i $Id: encoding.ml,v 1.17 2009-12-01 10:12:28 bobot Exp $ i*)

open Options

let queue = Queue.create ()

let reset () = match get_types_encoding () with
  | NoEncoding -> Queue.clear queue
  | Predicates -> Encoding_pred.reset ()
  | Stratified -> Encoding_strat.reset ()
  | SortedStratified -> Encoding_mono.reset ()
  | Recursive -> Encoding_rec.reset ()
  | Monomorph -> Monomorph.reset ()
  | MonoInst -> Encoding_mono_inst.reset ()

let push d = match get_types_encoding () with
  | NoEncoding -> Queue.add d queue
  | Predicates -> Encoding_pred.push d
  | SortedStratified -> Encoding_mono.push d
  | Stratified -> Encoding_strat.push d
  | Recursive -> Encoding_rec.push d
  | Monomorph -> Monomorph.push_decl d
  | MonoInst -> Encoding_mono_inst.push_decl d

let push ?(encode_inductive=true) ?(encode_algtype=true) 
    ?(encode_preds=true) ?(encode_funs=true) = function
  | Logic_decl.Dfunction_def (loc, id, d) when encode_funs ->
      List.iter push (PredDefExpansor.function_def loc id d)
  | Logic_decl.Dpredicate_def (loc, id, d) when encode_preds ->
      List.iter push (PredDefExpansor.predicate_def loc id d)
  | Logic_decl.Dinductive_def (loc, id, d) when encode_inductive ->
      List.iter push (PredDefExpansor.inductive_def loc id d)
  | Logic_decl.Dalgtype ls when encode_algtype ->
      List.iter push (PredDefExpansor.algebraic_type ls)
  | d -> push d

(*
let push d = match get_types_encoding () with
  | NoEncoding -> Queue.add d queue
  | _ -> push d
*)

let iter f = match get_types_encoding () with
  | NoEncoding -> Queue.iter f queue
  | Predicates -> Encoding_pred.iter f
  | Stratified -> Encoding_strat.iter f
  | SortedStratified -> Encoding_mono.iter f
  | Recursive -> Encoding_rec.iter f
  | Monomorph -> Monomorph.iter f
  | MonoInst -> Encoding_mono_inst.iter f

let symbol ((id,_) as s) = match get_types_encoding () with
  | Monomorph -> Monomorph.symbol s
  | _ -> Ident.string id
