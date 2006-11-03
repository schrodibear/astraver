(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
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

(*i $Id: encoding.ml,v 1.6 2006-11-03 11:55:28 marche Exp $ i*)

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
