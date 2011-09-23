(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Jc_env
open Jc_envset
open Jc_pervasives

type t = type_var_info

let type_var_from_string = let c = ref 0 in fun ?(univ=false) n -> incr c; 
  { jc_type_var_info_name = n;
    jc_type_var_info_tag = !c;
    jc_type_var_info_univ = univ}

let uid x = x.jc_type_var_info_tag

let name x = x.jc_type_var_info_name

let uname x =
  name x ^ string_of_int (uid x)

type typing_error = {f : 'a. Loc.position -> ('a, Format.formatter, unit, unit) format4 -> 'a}

type env = { typing_error : typing_error;
             mutable smap : t StringMap.t;
             mutable vmap : jc_type TypeVarMap.t}

let create x = {typing_error = x;
                smap = StringMap.empty;
                vmap = TypeVarMap.empty}

let reset env = env.smap <- StringMap.empty;env.vmap <- TypeVarMap.empty
  

(** Add substitution from string to type *)
let add_type_var env s = 
  if StringMap.mem s env.smap 
  then invalid_arg ("The same identifier appear twice as polymorphic variable in a function")
  else 
    (let n = (type_var_from_string ~univ:true s) in
    env.smap <- StringMap.add s n env.smap;
    n)

(*                    if subtype_strict te#typ ty then te
                     else
                       typing_error e#pos 
                         "type %a expected instead of %a" 
                         print_type ty print_type te#typ*)

let find_type_var env s = StringMap.find s env.smap

exception Not_subtype of jc_type * jc_type

let rec substruct st = function
  | (JCtag(st', _)) as pc ->
      if st == st' then true else
        let vi = struct_root st and vi' = struct_root st' in
        (vi == vi' && (root_is_union vi))
        || 
        begin match st.jc_struct_info_parent with
          | None -> false
          | Some(p, []) -> substruct p pc
          | Some(_p, _) -> assert false (* TODO *)
        end
  | JCroot vi ->
      struct_root st == vi

let rec dec_type ~subtype acc t1 t2 =
  let accorraise b = if b then acc else raise (Not_subtype (t1,t2)) in
  match t1,t2 with
    | JCTnative t1, JCTnative t2 ->
        accorraise (t1=t2 ||
         (* integer is subtype of real *)
            (subtype && match t1,t2 with 
               | Tinteger, Treal -> true
	       | _ -> false))
    | JCTenum ri1, JCTenum ri2 -> 
        accorraise (subtype && Num.ge_num ri1.jc_enum_info_min ri2.jc_enum_info_min &&
                      Num.le_num ri1.jc_enum_info_max ri2.jc_enum_info_max) 
    | JCTenum _, JCTnative (Tinteger | Treal) ->
        accorraise subtype
    | JCTnative Tinteger, JCTenum _ -> 
        accorraise false
    | JCTpointer(JCtag(s1, []), _, _), JCTpointer(pc, _, _) -> 
        accorraise (substruct s1 pc)
    | JCTpointer(JCroot v1, _, _), JCTpointer(JCroot v2, _, _) ->
         accorraise (v1 == v2)
    | JCTnull, (JCTnull | JCTpointer _) ->
        accorraise subtype
    | JCTlogic (s1,l1), JCTlogic (s2,l2) ->
        if s1=s2 then List.fold_left2 (dec_type ~subtype) acc l1 l2
        else raise (Not_subtype (t1,t2))
          (* No subtyping for this case, the equality is strict *)
    | JCTtype_var {jc_type_var_info_tag = t1}, 
        JCTtype_var {jc_type_var_info_tag = t2} when t1=t2-> acc
    | (JCTtype_var ({jc_type_var_info_univ = false} as tvar),t) 
    | (t,JCTtype_var ({jc_type_var_info_univ = false} as tvar)) -> (tvar,t)::acc
    | _ -> accorraise false

let rec subst_aux vmap a =
  match a with
    | JCTtype_var tvar -> 
        (try TypeVarMap.find tvar vmap
        with Not_found -> a)
    | JCTlogic (s,l) -> JCTlogic (s,List.map (subst_aux vmap) l)
    | a -> a

let subst env a = subst_aux env.vmap a

let rec occur_check tvar t =
  match t with
    | JCTlogic (_s,l) -> List.exists (occur_check tvar) l
    | JCTtype_var tvar2 -> TypeVarOrd.equal tvar tvar2
    | _ -> false

let rec add_subst env (tvar,t) = 
  assert (not tvar.jc_type_var_info_univ);
  let t = subst_aux env.vmap t in
  try
    let t2 = TypeVarMap.find tvar env.vmap in
    add_aux ~subtype:false env t2 t
  with Not_found ->     
    if occur_check tvar t then raise (Not_subtype (JCTtype_var tvar,t))
    else env.vmap <- TypeVarMap.add tvar t env.vmap
          
and add_aux ~subtype env t1 t2 =
  let acc = dec_type ~subtype [] t1 t2 in
  List.iter (add_subst env) acc

(*let subtype_strict = subtype ~allow_implicit_cast:false*)

(** Add an equality for unification *)
let add ?(subtype=true) env pos x y = 
  (*Format.printf "%a=%a@." print_type x print_type y;*)
  try
    add_aux ~subtype env x y
  with Not_subtype (t1,t2) -> 
    env.typing_error.f pos "%a and %a can't be unified" print_type t1 print_type t2

(** Get instances of a list of type variables, 
    return a substitution function *)
let instance l =
  let aux acc e =
    (* Only universally quantified variable can be instantiate *)
    assert e.jc_type_var_info_univ;
    let e_fresh = (type_var_from_string ~univ:false e.jc_type_var_info_name) in
    TypeVarMap.add e (JCTtype_var e_fresh) acc in
  let vmap = List.fold_left aux TypeVarMap.empty l in
  subst_aux vmap

open Pp
let print_smap fmt a = print_list comma (print_pair string print_type_var) fmt (StringMap.to_list a)

let print_vmap fmt a = print_list comma (print_pair print_type_var print_type) fmt (TypeVarMap.to_list a)

let print fmt uenv = Format.fprintf fmt "uenv : smap : %a@.vmap : %a@." print_smap uenv.smap print_vmap uenv.vmap

let subst_type_in_assertion uenv =
  Jc_iterators.map_term_in_assertion
    (fun t -> new Jc_constructors.term_with ~typ:(subst uenv t#typ) t)                                   
    
(*
Local Variables: 
compile-command: "unset LANG ; make -C .. byte"
End: 
*)
