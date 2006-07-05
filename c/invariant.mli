open Creport
open Info
open Ctypes
open Clogic
open Cenv
open Cnorm

val add_predicates : 
  Cast.ndecl Cast.located list -> Cast.ndecl Cast.located list

val add_typing_predicates :
  Cast.ndecl Cast.located list -> Cast.ndecl Cast.located list
