open Misc
open Vcg
open Logic
open Cc
open Format
open Astprinter
open Tags

(*val insert_text : GText.buffer -> string -> string -> unit*)

(*(val insert_string : GText.buffer -> string -> unit *)

val text_of_obligation :
  GText.view -> GText.view ->
  'a * string * (Cc.context_element list * Logic.predicate) -> bool -> unit
