(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id: pcicenv.ml,v 1.1 2001-08-15 21:08:52 filliatr Exp $ *)

open Names
open Term
open Sign

open Misc
open Util
open Types
open Ast

(* on red�finit add_sign pour �viter de construire des environnements
 * avec des doublons (qui font planter la r�solution des implicites !) *)

(* VERY UGLY!! find some work around *)
let modify_sign id t s =
  let t' = lookup_id_type id s in
  map_named_context (fun t'' -> if t'' == t' then t else t'') s

let add_sign (id,t) s =
  if mem_named_context id s then
    modify_sign id t s
  else
    add_named_assum (id,t) s

let cast_set c = mkCast (c, mkSet)

let set = mkCast (mkSet, mkType Univ.prop_univ)

(* [cci_sign_of env] construit un environnement pour CIC ne comprenant que
 * les objets fonctionnels de l'environnement de programes [env]
 *)

let cci_sign_of ren env =
  Env.fold_all 
    (fun (id,v) sign ->
       match v with
	 | Env.TypeV (Ref _ | Array _) -> sign
	 | Env.TypeV v -> 
	     let ty = Monad.trad_ml_type_v ren env v in
	     add_sign (id,cast_set ty) sign
	 | Env.Set -> add_sign (id,set) sign)
    env (Global.named_context ())

(* [sign_meta ren env fadd ini]
 * construit un environnement pour CIC qui prend en compte les variables
 * de programme. 
 * pour cela, cette fonction parcours tout l'envrionnement (global puis
 * local [env]) et pour chaque d�claration, ajoute ce qu'il faut avec la
 * fonction [fadd] s'il s'agit d'un mutable et directement sinon,
 * en partant de [ini].
 *)

let sign_meta ren env fast ini =
   Env.fold_all 
    (fun (id,v) sign ->
       match v with
	 | Env.TypeV (Ref _ | Array _ as v) -> 
	     let ty = Monad.trad_imp_type ren env v in
	     fast sign id ty
	 | Env.TypeV v -> 
	     let ty = Monad.trad_ml_type_v ren env v in
	     add_sign (id,cast_set ty) sign
	 | Env.Set -> add_sign (id,set) sign)
    env ini

let add_sign_d dates (id,c) sign =
  let sign =
    List.fold_left (fun sign d -> add_sign (at_id id d,c) sign) sign dates
  in
    add_sign (id,c) sign
 
let sign_of add ren env =
  sign_meta ren env
    (fun sign id c -> let c = cast_set c in add (id,c) sign)
    (Global.named_context ())

let result_of sign = function
    None   -> sign
  | Some (id,c) -> add_sign (id, cast_set c) sign
	
let before_after_result_sign_of res ren env =
  let dates = "" :: Rename.all_dates ren in
  result_of (sign_of (add_sign_d dates) ren env) res

let before_after_sign_of ren =
  let dates = "" :: Rename.all_dates ren in
  sign_of (add_sign_d dates) ren

let before_sign_of ren =
  let dates = Rename.all_dates ren in
  sign_of (add_sign_d dates) ren

let now_sign_of =
  sign_of (add_sign_d [])


(* environnement apr�s traduction *)

let trad_sign_of ren =
  sign_of
    (fun (id,c) sign -> add_sign (Rename.current_var ren id,c) sign)
    ren


