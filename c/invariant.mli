open Creport
open Info
open Ctypes
open Clogic
open Cenv
open Cnorm

val add_predicates : 
  Cast.ndecl Cast.located list -> Cast.ndecl Cast.located list

val pred_for_type : 
  Cast.nctype -> Cast.nterm -> Cast.npredicate

val add_typing_predicates :
  Cast.ndecl Cast.located list -> Cast.ndecl Cast.located list

val min_int : Ctypes.sign * Ctypes.cinteger -> string
val max_int : Ctypes.sign * Ctypes.cinteger -> string
