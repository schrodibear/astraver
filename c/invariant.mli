open Creport
open Info
open Ctypes
open Clogic
open Cenv
open Cnorm

val diff : 'a -> 'b Clogic.nterm -> 'b Clogic.nterm -> 'b Clogic.npredicate

val add_predicates : 
  Cast.ndecl Cast.located list -> Cast.ndecl Cast.located list
