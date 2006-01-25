open Pp
open Misc
open Util
open Vcg
open Logic
open Cc

type loc

val get_color : string -> string * string 

val tag_to_name : GText.tag -> string option

val insert_text : GText.buffer -> string -> ?loc:string option -> string -> unit

val insert_string : GText.buffer -> string -> unit

val get_location : string -> loc option

val text_of_obligation :
    GText.buffer ->
    'a * string * (Cc.context_element list * Logic.predicate) -> unit
