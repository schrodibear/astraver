(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: report.mli,v 1.1 2002-07-08 13:21:27 filliatr Exp $ i*)

open Format

exception Error of (Loc.t option) * Error.t

val report : formatter -> Error.t -> unit

val raise_located : Loc.t -> Error.t -> 'a 
val raise_unlocated : Error.t -> 'a
val raise_locop : Loc.t option -> Error.t -> 'a

