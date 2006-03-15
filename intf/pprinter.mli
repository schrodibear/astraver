open Misc
open Vcg
open Logic
open Cc
open Format
open Astprinter
open Tags

val text_of_obligation :
  GText.view -> GText.view ->
  'a * string * (Cc.context_element list * Logic.predicate) -> bool -> unit
