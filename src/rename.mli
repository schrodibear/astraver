(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: rename.mli,v 1.3 2002-03-13 10:01:37 filliatr Exp $ i*)

(* Abstract type for renamings 
 * 
 * Records the names of the mutables objets (ref, arrays) at the different
 * moments of the evaluation, called dates
 *)

type t

type date = string


val empty_ren : t
val update    : t -> date -> Ident.t list -> t
    (* assign new names for the given variables, associated to a new date *)
val next      : t -> Ident.t list -> t
    (* assign new names for the given variables, associated to a new
     * date which is generated from an internal counter *)
val push_date : t -> date -> t
    (* put a new date on top of the stack *)

val valid_date   : date -> t -> bool
val current_date : t -> date
val all_dates    : t -> date list

val current_var  : t -> Ident.t      -> Ident.t
val current_vars : t -> Ident.t list -> (Ident.t * Ident.t) list
    (* gives the current names of some variables *)

val avoid : t -> Ident.set -> t
val fresh : t -> Ident.t -> Ident.t * t
val fresh_many : t -> Ident.t list -> (Ident.t * Ident.t) list * t
    (* introduces new names to avoid and renames some given variables *)

val var_at_date  : t -> date -> Ident.t -> Ident.t
    (* gives the name of a variable at a given date *)
val vars_at_date : t -> date -> Ident.t list
                 -> (Ident.t * Ident.t) list
    (* idem for a list of variables *)  

(* pretty-printers *)

open Format

val print : formatter -> t -> unit
