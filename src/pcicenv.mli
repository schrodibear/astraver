
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: pcicenv.mli,v 1.2 2001-08-17 00:52:38 filliatr Exp $ *)

open Env
open Logic

(* Translation of local programs environments into Coq signatures.
 * It is mainly used to type the pre/post conditions in the good
 * environment *)

(* cci_sign_of: uniquement les objets purement fonctionnels de l'env. *)
val cci_sign_of : Rename.t -> local_env -> named_context

(* env. Coq avec seulement les variables X de l'env. *)
val now_sign_of : Rename.t -> local_env -> named_context

(* + les variables X@d pour toutes les dates de l'env. *)
val before_sign_of : Rename.t -> local_env -> named_context

(* + les variables `avant' X@ *)
val before_after_sign_of : Rename.t -> local_env -> named_context
val before_after_result_sign_of : ((Ident.t * constr) option)
                        -> Rename.t -> local_env -> named_context

(* env. des programmes traduits, avec les variables rennomées *)
val trad_sign_of : Rename.t -> local_env -> named_context

