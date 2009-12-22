(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Cc
open Logic
open Logic_decl
open Format

let map_product (f: 'a -> 'a list) (l:'a list) : 'a list list =
  List.fold_left 
    (fun prev_acc e ->
       let lr = f e in
       List.fold_left 
         (fun acc l -> List.fold_left (fun acc e -> (e::l)::acc) acc lr)
         [] prev_acc) [[]] l

(*let map_times (f: 'a -> 'b -> 'c) (l1:'a list) (l2:'b list) : 'c list =
  List.fold_left
    (fun 
*)

let loc = Loc.dummy_floc
let debug = Options.debug
let f2s (s,l,b,e) = Printf.sprintf "File %s, line %d, characters %d-%d" s l b e

let prefix = fun s -> "c_"^s
(* let suffix = "_c" *)
(* let var = "x" *)
let tvar = "_why_t"
(* let cpt = ref 0 *)
let injec c = c^"_injective"
(* let axiom c = c ^ "_to_" ^ (c^suffix) *)
let def c = "def_"^Ident.string c

(* The names for the new function symbols *)
let sort =  Ident.create (prefix "sort")

let is_const t = (* match Misc.normalize_pure_type t with *) match t with
  | PTint | PTbool | PTreal | PTunit -> true
  | _ -> false

(*let cname t =  match Misc.normalize_pure_type t with
  | PTint -> "int"
  | PTbool -> "bool"
  | PTreal -> "real"
  | PTunit -> "unit"
      (** TODO : better error handling here *)
  | _ -> failwith "this function should only be called on constant types"
let c2u t = (cname t)^"2u"
let s2c t = "s2"^(cname t)*)

(* This is the list of constant types which is handled as such *)
let htypes = [PTint; PTbool; PTreal; PTunit]

(* The monosorted stratified encoding introduces
   three new external types : a sort for syntactically 
   unsorted terms, one for sorted terms and one for 
   syntactic types *)
let utname = Ident.create (prefix "unsorted")
let stname = Ident.create (prefix "sorted")
let ttname = Ident.create (prefix "type")
let ut = PTexternal ([], utname)
let st = PTexternal ([], stname)
let tt = PTexternal ([], ttname)

(* one dumb type *)
let dtname = prefix "alpha"
let dtnameid = Ident.create dtname
let dt = PTexternal ([], dtnameid)

(* The prelude is a set of declarations that must be added
   to the context every time the encoding is used :*)
let eq_arity = (Ident.string Ident.t_eq, Env.empty_scheme (Predicate [st; st]))
let neq_arity = (Ident.string Ident.t_neq, Env.empty_scheme (Predicate [st; st]))

let builtin_poly = [Ident.t_eq;Ident.t_neq(*;Ident.if_then_else*)]
let builtin_poly = List.fold_left (fun s x -> Ident.Idset.add x s) Ident.Idset.empty builtin_poly

let builtin = [] (*[Ident.t_sub_int;Ident.t_add_int;Ident.t_mul_int;Ident.t_div_int;
               Ident.t_mod_int;Ident.t_neg_int;Ident.t_abs_int;
               Ident.t_gt_int;Ident.t_ge_int;Ident.t_eq_int;Ident.t_lt_int;Ident.t_le_int;Ident.t_neq_int;
              ]*)

let builtin = List.fold_left (fun s x -> Ident.Idset.add x s) builtin_poly builtin

let ident_of_close_type t = 
  let rec aux fmt = function
    | PTint -> fprintf fmt "int"
    | PTbool -> fprintf fmt "bool"
    | PTunit -> fprintf fmt "unit"
    | PTreal -> fprintf fmt "real"
    | PTexternal ([],id) -> fprintf fmt "%a" Ident.print id
    | PTvar {tag=_t; type_val=None} -> assert false (* close type *)
    | PTvar {tag=_t; type_val=Some pt} -> aux fmt pt
    | PTexternal (l,id) -> fprintf fmt "%aI%a" 
        (Pp.print_list (Pp.constant_string "I") aux) l Ident.print id in
  let b = Buffer.create 10 in
  Format.bprintf b "%a@?" aux t;
  Ident.create (Buffer.contents b)

module E = struct
  open Mapenv
  open Env
  
  module Idmap = Ident.Idmap
  module Idset = Ident.Idset

  type t = { 
    (** assoc the name of a function and one instanciation 
       with the name of the function coded *)
    instances : Ident.t Inst_Map.t;
    (** assoc the name of a function to its arities *)
    arities : logic_type scheme Idmap.t;
    (** assoc with each type to be monomorphised 
        the name of the monomorphe type*)
    mono : Ident.t PT_Map.t;
    (** assoc with each type at the edge of the monomorph 
        world the logic used in the encoding *)
    encode : Ident.t PT_Map.t;
    (** used for a .... *)
    def_logic : (Ident.t * Logic.logic_type Env.scheme) list Idmap.t;
    def_type : (Ident.t * int) list Idmap.t;
  }

  let print fmt env = 
    Format.fprintf fmt "instances :%a@." 
      (Pp.print_iter2 Inst_Map.iter Pp.semi Pp.comma
         (Pp.print_pair Ident.print
            (Pp.print_list Pp.comma Util.print_pure_type)) 
         Ident.print) 
      env.instances;
    Format.fprintf fmt "arities :%a@." 
      (Pp.print_iter2 Idmap.iter Pp.semi Pp.comma
         Ident.print
         (Util.print_scheme Util.print_logic_type))
      env.arities;
    Format.fprintf fmt "mono :%a@." 
      (Pp.print_iter2 PT_Map.iter Pp.semi Pp.comma
         Util.print_pure_type
         Ident.print)
      env.mono;
    Format.fprintf fmt "encode :%a@." 
      (Pp.print_iter2 PT_Map.iter Pp.semi Pp.comma 
         Util.print_pure_type 
         Ident.print) 
      env.encode;
    Format.fprintf fmt "def_logic :%a@." 
      (Pp.print_iter2 Idmap.iter Pp.semi Pp.comma
         Ident.print
         (Pp.print_list Pp.comma 
            (Pp.print_pair
               Ident.print
               (Util.print_scheme Util.print_logic_type))))
      env.def_logic;
    Format.fprintf fmt "def_type :%a@." 
      (Pp.print_iter2 Idmap.iter Pp.semi Pp.comma 
         Ident.print 
         (Pp.print_list Pp.comma 
            (Pp.print_pair 
               Ident.print 
               Pp.int))) 
      env.def_type

    
  (** create the environnement from a list of close type
      to monomorphise *)
  let create l =
    let s = add_subtype_list PT_Set.empty l in
    let m = PT_Set.fold 
      (fun e m -> PT_Map.add e (ident_of_close_type e) m) s PT_Map.empty in
    {instances = Inst_Map.empty;
     mono = m;
     encode = PT_Map.empty;
     arities = Idmap.empty;
     def_logic = Idmap.empty;
     def_type = Idmap.empty}
     
  type w = 
    | Mono of pure_type
    | Enco of term

  let print_w fmt = function
    | Mono ty -> Format.fprintf fmt "Mono %a" Util.print_pure_type ty
    | Enco t -> Format.fprintf fmt "Enco %a" Util.print_term t


  (** The encoded type are represented by tt *)
  let reduce_to_type = function 
    | Mono x -> x
    | Enco _t -> dt

 (** The encoded term are represented by u *)
  let reduce_to_type_neg = function 
    | Mono x -> x
    | Enco _t -> st

(** The encoded term are represented by s *)
  let reduce_to_type_pos = function 
    | Mono x -> x
    | Enco _t -> ut

  (** The instantiated types don't need encoding *)
  let reduce_to_term = function 
    | Mono _x -> None
    | Enco t -> Some t

  (** Keep the builtin type for builtin type *)
  let name_of_mono v = function
    | PTint | PTbool | PTreal | PTunit as t -> t
    | _ -> PTexternal ([],v)

  let type_of_mono _v k = k
  let ident_of_mono v _k = v

  let trad_type env fv_t t =
    (*if debug then Format.eprintf "trad_type : %a@." Util.print_pure_type t;*)
    let rec normalize_pure_type = function
        | PTint | PTbool | PTreal | PTunit as t -> t
        | PTvar {type_val=Some t} -> normalize_pure_type t
        | PTvar ({type_val=None} as v) as t ->
              (try
                 match Vmap.find v fv_t with
                   | Mono ty -> ty
                   | Enco _ -> t
               with Not_found -> assert false) (* term not closed *)
        | PTexternal (l,s) -> PTexternal (List.map normalize_pure_type l,s) in
    let rec aux t =
      try
        Mono (name_of_mono (PT_Map.find t env.mono) t)
      with Not_found ->
        match t with
          | PTint | PTbool | PTreal | PTunit ->
              (try 
                 Enco (Tapp (PT_Map.find t env.encode,[],[]))
               with Not_found -> assert false
                 (* the builtin type must be in mono or encode *))
          | PTvar {type_val=Some t} -> aux t
          | PTvar ({type_val=None} as v) ->
              (try
                 Vmap.find v fv_t
               with Not_found -> assert false) (* term not closed *)
          | PTexternal ([],s) when s == dtnameid -> Enco (Tvar dtnameid) (*that case appear only when we instantiate a logic or type, dumb value *)
          | PTexternal (l,s) -> 
              let l = List.map aux l in
              let l2 = List.map reduce_to_type l in
              try
                let s = PT_Map.find (PTexternal (l2,s)) env.encode in
                let l = List.rev (List.fold_left (fun l e ->
                                                    match e with
                                                      | Mono _ -> l
                                                      | Enco t -> t::l) [] l) in
                Enco (Tapp(s,l,[]))
              with Not_found -> 
                if debug then
                  Format.eprintf "Notfound type = %a -> %a@." Util.print_pure_type t Util.print_pure_type (PTexternal (l2,s));
                  assert false
                  (* There is an instanciation for any instanciation *)
    in aux (normalize_pure_type t)

  let trad_to_type env fv_t x = reduce_to_type (trad_type env fv_t x)
  let trad_to_type_pos env fv_t x = reduce_to_type_pos (trad_type env fv_t x)
  let trad_to_type_neg env fv_t x = reduce_to_type_neg (trad_type env fv_t x)
  let trad_to_term env fv_t x = reduce_to_term (trad_type env fv_t x)

  let rec all_possible which env acc l nargs = function
    | 0 ->  (l,nargs)::acc
    | n -> let acc = PT_Map.fold 
        (fun k v acc -> all_possible which env acc ((which v k)::l) nargs (n-1)) env.mono acc in
      all_possible which env acc ((which dtnameid dt)::l) (nargs+1) (n-1)

  (** add a polymorphe (or not, but make_world ensures it (not anymore ;))) type to take into account. *)
  let add_type env tid nargs = 
    let allp = all_possible (fun v k -> (v,k)) env [] [] 0 nargs in
    let encode,l = List.fold_left
      (fun (encode,ll) (vk,nargs) ->
         let l = PTexternal (List.map snd vk,tid) in
         let encodell =
           if PT_Map.mem l env.mono 
           then encode,ll 
           else begin
             let l = List.map (fun (v,k) -> name_of_mono v k) vk in
             let l = PTexternal (l,tid) in
             let lid = ident_of_close_type l in
             PT_Map.add l lid encode,(lid,nargs)::ll
           end in encodell)
      (env.encode,[]) allp in
    {env with encode = encode;
       def_type = Idmap.add tid l env.def_type}

  let get_type env t = 
    Idmap.find t env.def_type
    
  let add_logic_aux env tid arities =
    let nargs = Vset.cardinal arities.Env.scheme_vars in
    let allp = all_possible type_of_mono env [] [] 0 nargs in
    let _,instances,l = List.fold_left
      (fun (lidset,instances,l) (inst,_) -> 
         let arities = instantiate_logic_type arities inst in
         (*if debug then
           Format.eprintf "add_logic : arities : %a@." Util.print_logic_type arities;*)
         let l_ty,arities = 
           match arities with
             | Function(args,ret) -> 
                 let args,ret = List.map (trad_to_type_neg env Vmap.empty) args,
                   (trad_to_type_pos env Vmap.empty) ret in
                 ret::args,Function(args,ret)
             | Predicate(arg) ->
                 let arg = List.map (trad_to_type_neg env Vmap.empty) arg in
                 arg,Predicate(arg) in
         let l_ty = PTexternal (l_ty,tid) in
         (* If the identifier is not polymorph then we keep its name *)
         let lid = if nargs = 0 
         then tid
         else ident_of_close_type l_ty in
         let inst = List.map (trad_to_type env Vmap.empty) inst in
         let instances = Inst_Map.add (tid,inst) lid instances in
         let lidset,l = if Idset.mem lid lidset 
         then lidset,l
         else Idset.add lid lidset,(lid,Env.empty_scheme arities)::l in
         lidset,instances,l)
      (Idset.empty,env.instances,[]) allp in
    {env with instances = instances;
       def_logic = Idmap.add tid l env.def_logic;
       arities = Idmap.add tid arities env.arities}

  let add_logic_poly env tid arities =
    let nargs = Vset.cardinal arities.Env.scheme_vars in
    let allp = all_possible type_of_mono env [] [] 0 nargs in
    let instances = List.fold_left
      (fun instances (inst,_) -> 
         let instances = Inst_Map.add (tid,inst) tid instances in
         instances) env.instances allp in
    {env with instances = instances;
       def_logic = Idmap.add tid [tid,arities] env.def_logic;
       arities = Idmap.add tid arities env.arities}

  let add_logic env tid arities =
    if Idset.mem tid builtin_poly
    then add_logic_poly env tid arities
    else add_logic_aux env tid arities

  let get_logic env id =
    Idmap.find id env.def_logic
    
  let give_inst env scheme = 
    let nargs = Vset.cardinal scheme.Env.scheme_vars in
    let vargs = Vset.elements scheme.Env.scheme_vars in
    let allp = all_possible type_of_mono env [] [] 0 nargs in
    let allp = List.map 
      (fun (inst,_) -> 
         let cpt = ref 0 in
         List.fold_left2 
           (fun m ty v -> 
              let ty = 
                if ty == dt 
                then (incr cpt;Enco (Tvar (Ident.create (tvar^(string_of_int !cpt)))))
                else Mono ty in
              Vmap.add v ty m)
           Vmap.empty inst vargs) allp in
    allp,scheme.Env.scheme_type

  let instance_of env fv_t id inst = 
    if Idset.mem id builtin_poly
    then id
    else
      let inst2 = List.map (trad_type env fv_t) inst in
      let inst3 = List.map reduce_to_type inst2 in
        try
          Inst_Map.find (id,inst3) env.instances
        with Not_found as e -> 
          Format.eprintf "Not_found : instance_of : id=%a@.inst=%a@.inst2=%a@.inst3=%a" Ident.print id Util.print_instance inst (Pp.print_list Pp.semi print_w) inst2 Util.print_instance inst3;
            raise e

  let type_of env id inst =
    try
      let ty = Idmap.find id env.arities in
      let ty = instantiate_logic_type ty inst in
      ty
    with Not_found as e -> 
      Format.eprintf "type_of : unknown ident : %a" Ident.print id;
      raise e
   
  let rec get_fun env fv_t id inst =
    let id_inst = instance_of env fv_t id inst in
    let ty = type_of env id inst in
    match ty with
      | Function (arg,_ret) -> (id_inst,(List.map (fun x -> reduce_to_term (trad_type env fv_t x)) arg))
      | Predicate _ -> assert false

  let rec get_pred env fv_t id inst =
    let id_inst = instance_of env fv_t id inst in
    let ty = type_of env id inst in
    match ty with
      | Function _ -> assert false
      | Predicate arg -> (id_inst,(List.map (fun x -> reduce_to_term (trad_type env fv_t x)) arg))

end

let prelude env =
  (* first the three new types *)
  (Dtype (loc, utname, []))::
    (Dtype (loc, stname, []))::
    (Dtype (loc, ttname, []))::
    (Dlogic (loc, sort, Env.empty_scheme (Function ([tt; ut], st))))::
  (Mapenv.PT_Map.fold (fun k v acc -> 
                         if is_const k then acc
                         else (Dtype (loc, v, []))::acc) env.E.mono [])
  (* the function symbols representing constant types *)
(*  @
 (List.map (fun t -> (Dlogic (loc, prefix (cname t),
			       Env.empty_scheme (Function ([], tt)))))
     htypes)
  (* the sorting and conversion functions *)
  @
  (List.map (fun t ->
	       (Dlogic (loc, c2u t, 
			Env.empty_scheme (Function ([t], ut)))))
     htypes)
  @
  (List.map (fun t ->
	       (Dlogic (loc, s2c t,
			Env.empty_scheme (Function ([st], t)))))
     htypes)*)

(* Functions that replace polymorphic types by S,T,U and constants *)
(*let typify ptl = List.map (fun _ -> tt) ptl

let sortify env t pt = 
  match pt with
    | PTint | PTbool | PTreal | PTunit -> pt
    | PTvar _ -> t
    | PTexternal (_,_) -> t

let monoify env = List.map (sortify st)
*)
let sort_of_c = function
  | ConstInt _ -> PTint
  | ConstBool _ -> PTbool
  | ConstUnit -> PTunit
  | ConstFloat _ -> PTreal

(* Function that plunges a term under its type information. *)
(* Uses an assoc. list of tags -> idents for type variables *)
(*let plunge fv term pt =
  let rec leftt pt =
    match pt with
      |	PTint | PTbool | PTreal | PTunit ->
	  Tapp (Ident.create (prefix (cname pt)), [], [])
      | PTvar ({type_val = None} as var) -> 
	  let t = 
	    try List.assoc var.tag fv
	    with Not_found ->
	      let s = string_of_int var.tag in
		(print_endline ("[plunge] unknown vartype : "^s); 
		 Format.eprintf "term = %a@." Util.print_term term;
		 s)
	  in
	    Tvar (Ident.create t)
      | PTvar {type_val = Some pt} -> leftt pt
      | PTexternal (ptl, id) -> Tapp (id, List.map (fun pt -> leftt pt) ptl, [])
  in
    Tapp (Ident.create sort,[leftt pt; term],[])
*)
let plunge_if_needed term = function
  | None -> term
  | Some ty_term -> Tapp (sort,[ty_term; term],[])
  

(* Function that strips the top most sort application, for terms bound
   in let-ins *)
(*let strip_topmost t =
  match t with
    | Tapp (symb, [encoded_ty; encoded_t], []) when symb = sort ->
	encoded_t
    | _ -> t
*)
(*let get_arity id =
  let arity =
    try List.assoc (Ident.string id) !arities
    with e -> (print_endline ("Encoding_mono.get_arity: unknown arity for "^(Ident.string id))); raise e in
    match arity.Env.scheme_type with
	Function (ptl, rt) -> ptl, rt
      | Predicate ptl -> ptl, PTbool (* ce PTbool est arbitraire et inutilisÃ© *)

(* Ground instanciation of an arity (to be plunged under) *)
let instantiate_arity id inst =
  let arity =
    try List.assoc (Ident.string id) !arities
    with e -> (print_endline ("Encoding_mono.instantiate_arity: unknown arity for "^(Ident.string id))); raise e in
  let (vs, log_type) = Env.specialize_logic_type arity in
    if debug then 
      (print_string "\t{";
       Env.Vmap.iter (fun _ v -> Printf.printf "%d" v.tag) vs;
       print_endline "}");
    match log_type with
	Function (ptl, rt) ->
	  if debug then Printf.printf "Instantiate : %d vars - %d types\n"
	    (Env.Vmap.fold (fun _ _ n -> n + 1) vs 0) (List.length inst);
	  ignore 
	    (Env.Vmap.fold (fun _ v l -> 
			      (match l with [] -> []
				 | a::q -> (v.type_val <- Some a; q)))
	       vs (List.rev inst));
	  rt
      | Predicate ptl ->
	  ignore 
	    (Env.Vmap.fold (fun _ v l -> 
			      (match l with [] -> []
				 | a::q -> (v.type_val <- Some a; q)))
	       vs (List.rev inst));
	  PTbool
*)
(* Translation of a term *)
(* [fv] is a map for type variables, [lv] for term variables,
   and [rt] is the type of this term in the arity of its
   direct superterm. *)
let rec translate_term env fv_t = function
  | Tvar _ | Tconst _ as t -> t
  | Tapp (id, tl, inst) ->
      let id,arg = E.get_fun env fv_t id inst in
      let tl = List.map (translate_term env fv_t) tl in
      let tl = List.map2 plunge_if_needed tl arg in
      Tapp (id, tl, [])
  | Tderef id as t -> print_endline ("id in Tderef : "^(Ident.string id)); t
  | Tnamed(_,t) -> translate_term env fv_t t

(* Generalizing a predicate scheme with foralls (can add a trigger) *)
(* This function is used to explicitely quantify over syntactic type 
   variables that were implicitely quantified at first. *)
let rec lifted l p t =
  let l = Env.Vmap.fold (fun _ e l -> 
                           match e with
                             | E.Enco (Tvar e) -> e::l 
                             | E.Enco _ -> assert false
                             | E.Mono _ -> l) l [] in
  let rec aux l =
    match l with [] -> p
      | s::[] ->
	  Forall(false, s, s, tt, t, p)
      | s::q ->
	  Forall(false, s, s, tt, [], aux q) in
  aux l
	
let rec lifted_t l p tr =
  match l with [] -> p
    | (a,t)::[] -> (Forall(false, a, a, t, tr, p))
    | (a,t)::q ->  (Forall(false, a, a, t, [], lifted_t q p tr))
(*
let rec lifted_ctxt l cel =
  (List.map (fun (_,s) -> Svar(Ident.create s, tt)) l)@cel
*)
(* Translation of a predicate *)
let rec translate_pred env fv_t = function
(*   | Papp (id, [a; b], [t]) when Ident.is_eq id && is_const t -> *)
(*       Papp (id, [translate_term fv lv t a; translate_term fv lv t b], []) *)
  | Papp (id, tl, inst) ->
      let id,arg = E.get_pred env fv_t id inst in
      let tl = List.map (translate_term env fv_t) tl in
      let tl = List.map2 plunge_if_needed tl arg in
      Papp (id, tl, [])
  | Plet (id, n, pt, t, p) -> 
      let t = translate_term env fv_t t in
      let pt = E.trad_to_type_pos env fv_t pt in
      let p = translate_pred env fv_t p in
	Plet (id, n, pt, t, p)
  | Pimplies (iswp, p1, p2) ->
      Pimplies (iswp, translate_pred env fv_t p1, translate_pred env fv_t p2)
  | Pif (t, p1, p2) ->
   (** Il faut que Bool soit dans l'ensemble S, 
       sinon il faut redéfinir Pif dans une axiomatique *)
      Pif (translate_term env fv_t t,
           translate_pred env fv_t p1, translate_pred env fv_t p2)
  | Pand (iswp, issym, p1, p2) ->
      Pand (iswp, issym, translate_pred env fv_t p1, translate_pred env fv_t p2)
  | Por (p1, p2) ->
      Por (translate_pred env fv_t p1, translate_pred env fv_t p2)
  | Piff (p1, p2) ->
      Piff (translate_pred env fv_t p1, translate_pred env fv_t p2)
  | Pnot p ->
      Pnot (translate_pred env fv_t p)
  | Forall (iswp, id, n, pt, _tl, p) ->
      let pt = E.trad_to_type_pos env fv_t pt in
      let tl = (*translate_triggers env fv_t p tl*) [] in
      Forall (iswp, id, n, pt, tl, translate_pred env fv_t p)
  | Forallb (iswp, p1, p2) ->
      Forallb (iswp, translate_pred env fv_t p1, translate_pred env fv_t p2)
  | Exists (id, n, pt, p) ->
      let pt = E.trad_to_type_pos env fv_t pt in
      Exists (id, n, pt, translate_pred env fv_t p)
  | Pnamed (s, p) ->
      Pnamed (s, translate_pred env fv_t p)
  | _ as d -> d
(*
and translate_pattern env fv lv p = function
  | TPat t -> 
      let rec lookfor_term fv lv acc rt = function
        | t2 when Misc.eq_term t t2 -> 
            (translate_term fv lv rt t2)::acc
        | Tvar _ | Tconst _ | Tderef _ -> acc
        | Tapp (id, tl, inst) ->
            let ptl, pt = get_arity id in
            List.fold_left2 (lookfor_term fv lv) acc ptl tl
        | Tnamed(_,t2) -> lookfor_term fv lv acc rt t2 in
      let rec lookfor_term_in_predicate fv lv acc = function
        | Pif (t, p1, p2) ->
            let acc = lookfor_term fv lv acc PTbool t in
            let acc =  lookfor_term_in_predicate fv lv acc p1 in
            let acc =  lookfor_term_in_predicate fv lv acc p2 in
            acc
        | Papp (id, tl, inst) ->
            let arity,_ = get_arity id in
	    List.fold_left2 (lookfor_term fv lv) acc arity tl
        | Plet (_, n, pt, t, p) -> 
            let acc = lookfor_term fv lv acc pt t in
	    lookfor_term_in_predicate fv ((n,pt)::lv) acc p
        | Forall (_, _, n, pt, _, p) | Exists (_, n, pt, p) ->
            lookfor_term_in_predicate fv ((n,pt)::lv) acc p
        | Pimplies (_, p1, p2) | Pand (_ , _, p1, p2) | Por (p1, p2) 
        | Piff (p1, p2) | Forallb (_, p1, p2) ->
            lookfor_term_in_predicate fv lv (lookfor_term_in_predicate fv lv acc p2) p1
        | Pnot p | Pnamed (_, p) -> lookfor_term_in_predicate fv lv acc p 
        | Pvar _|Pfalse|Ptrue -> acc in
      let r = (lookfor_term_in_predicate fv lv [] p) in
      Format.printf "%a : %a@." Util.print_term t (Pp.print_list Pp.comma Util.print_term) r;
      List.map (fun x -> TPat x) r
(*
  let rec translate_term_for_pattern fv lv = function
      (* mauvaise traduction des triggers mais ...
         Le type n'étant pas forcement le même 
         les plunges internes peuvent ne pas être les 
         même que dans le body de la quantification *)
      | Tvar _ as t -> t
      | Tapp (id, tl, inst) ->
      let ptl, pt = get_arity id in
      let trans_term = Tapp (id, List.map2 (translate_term fv lv) ptl tl, []) in
      let _ = instantiate_arity id inst in
      trans_term
      | Tconst (_) as t -> t
      | Tderef _ as t -> t
      | Tnamed(_,t) -> translate_term_for_pattern fv lv t in
      TPat (translate_term_for_pattern fv lv t)
*)
  | PPat p -> [PPat (translate_pred fv lv p)]

and translate_triggers fv lv p tl =
  List.fold_left (fun acc e -> List.rev_append (map_product (translate_pattern fv lv p) e) acc) [] tl
*)

(* The core *)
let queue = Queue.create ()

let make_list x = 
  let rec aux acc = function
    | 0 -> acc
    | n -> aux (x::acc) (n-1) in
  aux []

let rec translate_assertion env iter_fun d = 
  let ta env d = translate_assertion env iter_fun d in
  try (match d with
         | Dalgtype _ -> assert false
(* A type declaration is translated as new logical function, the arity of *)
(* which depends on the number of type variables in the declaration *)
  | Dtype (loc, ident, _vars) ->
      let terms = E.get_type env ident in
      List.iter 
        (fun (ident,nargs) ->
           let ty = Env.empty_scheme (Function (make_list tt nargs, tt))  in
             iter_fun (Dlogic (loc, ident, ty))) terms;
      env
(* In the case of a logic definition, we redefine the logic symbol  *)
(* with types u and s, and its complete arity is stored for the encoding *)
  | Dlogic (loc, ident, _arity) -> 
(*
      Format.eprintf "Encoding_mono: adding %s in arities@." ident;
*)
      let logics = E.get_logic env ident in
      List.iter 
        (fun (ident,ty) ->
           iter_fun (Dlogic (loc,ident, ty))) logics;
      env
(* A predicate definition can be handled as a predicate logic definition + an axiom *)
  | Dpredicate_def (loc, ident, pred_def_sch) ->
      let (argl, pred) = pred_def_sch.Env.scheme_type in
      let rootexp = (Papp (ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
      let env = ta env (Dlogic (loc, ident, (Env.generalize_logic_type (Predicate (snd (List.split argl)))))) in
      let env = ta env (Daxiom (loc, def ident, (Env.generalize_predicate
				      (lifted_t argl (Piff (rootexp, pred)) [[PPat rootexp]])))) in
      env
(* A function definition can be handled as a function logic definition + an axiom *)
  | Dinductive_def(_loc, _ident, _inddef) ->
      failwith "encoding mono: inductive def not yet supported"
  | Dfunction_def (loc, ident, fun_def_sch) ->
(*       let _ = print_endline ident in *)
      let (argl, rt, term) = fun_def_sch.Env.scheme_type in
      let rootexp = (Tapp (ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
      let env = ta env (Dlogic (loc, ident, (Env.generalize_logic_type (Function (snd (List.split argl), rt))))) in
      let env = ta env (Daxiom (loc, def ident,
		    (Env.generalize_predicate
		       (lifted_t argl (Papp (Ident.t_eq, [rootexp; term], [])) [[TPat rootexp]])))) in
      env
(* Axiom definitions *)
  | Daxiom (loc, ident, pred_sch) ->
      let insts,p_inst = E.give_inst env pred_sch in
      if debug then
        Format.eprintf "axiom : insts : %a@." 
          (Pp.print_list Pp.comma 
             (Pp.print_iter2 Env.Vmap.iter Pp.semi Pp.comma
                Util.print_type_var
                E.print_w)) insts;
      List.iter (fun fv_t ->
                   let pred = translate_pred env fv_t p_inst in
                   let new_axiom = Env.empty_scheme (lifted fv_t pred []) in
                   iter_fun (Daxiom (loc, ident, new_axiom))) insts;
      env
(* A goal is a sequent : a context and a predicate and both have to be translated *)
  | Dgoal (loc, expl, ident, s_sch) ->
      begin try
	let new_cel =
	  List.map
	    (fun s -> 
	       match s with
		   Spred (id, p) -> 
		    Spred (id, translate_pred env Env.Vmap.empty p)
		 | Svar (id, t) ->
                     let t = E.trad_to_type_pos env Env.Vmap.empty t in
                     Svar (id, t))
	    (fst (s_sch.Env.scheme_type)) in
	let new_sequent =
	  Env.empty_scheme
	    (new_cel,
	     translate_pred env Env.Vmap.empty (snd (s_sch.Env.scheme_type))) in
	iter_fun (Dgoal (loc, expl, ident, new_sequent))
      with Not_found -> 
	Format.eprintf "Exception caught in : %a\n" Util.print_decl d;
	iter_fun (Dgoal (loc, expl, ident, Env.empty_scheme([],Pfalse)));
      end;env)
  with Not_found -> 
    Format.eprintf "Exception caught in : %a\n" Util.print_decl d;
    raise Not_found

(** We take the type monomorph 
    and the type used in monomorph axioms :
    we want the traduction to be the identity 
    on the monomorph fragment*)
module PT_Set = Mapenv.PT_Set

let _PT_Set_add = Mapenv._PT_Set_add_normalize

let rec make_logic_type world id tl inst =
  try
    let (v,logic) = Env.find_global_logic id in
    Env.instantiate_specialized v inst;
    let world = match logic with
      | Function (arg,rt) ->  List.fold_left (fun s x -> _PT_Set_add x s)  world (rt::arg)
      | Predicate arg -> List.fold_left (fun s x -> _PT_Set_add x s) world arg in
    List.fold_left make_world_term world tl
  with Not_found as e -> Format.eprintf "Notfound : make_logic_type : %a@." Ident.print id; raise e

and make_world_term world = function
  | Tvar _ | Tderef _  -> world
  | Tconst c -> _PT_Set_add (sort_of_c c) world
  | Tapp (id,tl,inst) ->  make_logic_type world id tl inst
  | Tnamed (_,t) -> make_world_term world t

let rec make_world_predicate world = function
  | Pvar _ | Ptrue | Pfalse -> world
  | Pnot p | Pnamed (_,p) -> make_world_predicate world p
  | Pimplies(_,p1,p2) | Pand(_,_,p1,p2) | Por(p1,p2) | Piff(p1,p2) 
  | Forallb(_,p1,p2) -> make_world_predicate (make_world_predicate world p1) p2
      
  | Pif(t,p1,p2) -> 
      let world = make_world_term world t in
      let world = make_world_predicate (make_world_predicate world p1) p2 in
      world
  | Plet (_,_,ty,t,p) ->
      let world = make_world_term world t in
      let world = make_world_predicate world p in
      _PT_Set_add ty world
  | Forall(_,_,_,ty,_,p) | Exists(_,_,ty,p) ->
      let world = make_world_predicate world p in
      _PT_Set_add ty world
  | Papp(id,tl,inst) -> make_logic_type world id tl inst


let make_world_context_element world = function
  | Svar (_,ty) -> _PT_Set_add ty world
  | Spred (_,p) -> make_world_predicate world p

let make_world_sorted ~monotype ~monosig ~monodef world  = function
  | Dalgtype _ -> assert false
  | Dtype(_,s,[]) -> if monotype 
    then _PT_Set_add (PTexternal([],s)) world
    else world
  | Dlogic(_,_,sch) when Env.Vset.is_empty sch.Env.scheme_vars -> 
      if monosig then
      (match sch.Env.scheme_type with
         | Function (arg,rt) ->  List.fold_left (fun s x -> _PT_Set_add x s)  world (rt::arg)
         | Predicate arg ->  List.fold_left (fun s x -> _PT_Set_add x s)  world arg)
      else world
  | Dpredicate_def(_,_,sch) when Env.Vset.is_empty sch.Env.scheme_vars ->
        let world =      
          if monosig then
            List.fold_left (fun world (_,ty) -> _PT_Set_add ty world) world 
              (fst sch.Env.scheme_type) 
          else world in
        if monodef then
        make_world_predicate world (snd sch.Env.scheme_type)
        else world
      
  | Dinductive_def(_,_,sch) when Env.Vset.is_empty sch.Env.scheme_vars ->
      let world = if monosig then List.fold_left (fun s x -> _PT_Set_add x s)  world (fst sch.Env.scheme_type) else world in
      if monodef then
        List.fold_left (fun world (_,p) -> make_world_predicate world p) world
          (snd sch.Env.scheme_type)
      else world
  | Dfunction_def(_,_,{Env.scheme_vars =v;scheme_type=(tyl,tyr,t)}) 
      when Env.Vset.is_empty v ->
      let world = if monosig then List.fold_left (fun world (_,ty) -> _PT_Set_add ty world) world tyl else world in
      let world = if monosig then _PT_Set_add tyr world else world in
      if monodef then
        make_world_term world t
      else world
  | Daxiom(_,_,sch) when Env.Vset.is_empty sch.Env.scheme_vars ->
      make_world_predicate world sch.Env.scheme_type
  | Dgoal (_,_,_,{Env.scheme_vars =v;scheme_type=(con,p)}) 
      when Env.Vset.is_empty v ->
      let world = make_world_predicate world p in
      List.fold_left make_world_context_element world con
  | Dgoal _ -> assert false (* Dgoal must have been monomorphised *)
  | _ -> world (* Polymorph case *)

let make_world_just_goal world  = function
  | Dgoal (_,_,_,{Env.scheme_vars =v;scheme_type=(con,p)}) 
      when Env.Vset.is_empty v ->
      let world = make_world_predicate world p in
      List.fold_left make_world_context_element world con
  | Dgoal _ -> assert false (* Dgoal must have been monomorphised *)
  | _ -> world

let make_world_none world _ = world

let make_world = match Options.monoinstworldgen with
  | Options.MonoinstBuiltin -> make_world_none
  | Options.MonoinstSorted -> make_world_sorted ~monotype:true ~monodef:true ~monosig:true
  | Options.MonoinstGoal -> make_world_just_goal
  | Options.MonoinstPremises -> make_world_sorted ~monotype:false  ~monodef:true ~monosig:false

let monomorph_goal acc = function
  | Dgoal (loc,vc,id,sch) ->
      let cpt = ref 0 in
      let fv = Env.Vset.fold
	(fun _ acc -> 
	   cpt := !cpt + 1; 
	   (Ident.create (tvar^(string_of_int !cpt)))::acc)
	(sch.Env.scheme_vars) [] in
      let inst = List.map (fun x -> 
                             Env.add_type Loc.dummy_position [] x;
                             PTexternal ([],x)) fv in
      let p = Env.instantiate_sequent sch inst in
      let acc = List.fold_left (fun acc x -> Dtype (loc,x,[])::acc) acc fv in
      Dgoal (loc,vc,id,Env.empty_scheme p)::acc
  | x -> x::acc

let push_decl a = Queue.add a queue

let output_world world env =
  let print_world fmt = PT_Set.iter (fprintf fmt "%a;@." Util.print_pure_type) in
  let print_map fmt = Mapenv.PT_Map.iter (fun k v -> fprintf fmt "%a \"%a\";@." Util.print_pure_type k Ident.print v) in
  Format.printf "{%t}{%a}{%a}{%a}@." 
    (fun fmt -> Env.iter_type (fun id sch -> fprintf fmt "%a %i;@." Ident.print id sch))
    print_world world
    print_map env.E.mono
    print_map env.E.encode;
  exit 0

let iter f =
  (* monomorph the goal *)
  let decls = Queue.fold monomorph_goal [] queue in
  let decls = List.rev decls in
  if debug then Format.eprintf "Goal monomorphised@.";
  (* Find the type to monomorph *)
  let world = List.fold_left make_world PT_Set.empty decls in
  let world = List.fold_left (fun s x -> _PT_Set_add x s) world htypes in
  if debug then 
    Format.eprintf "world :%a@." (Pp.print_list Pp.comma Util.print_pure_type) (PT_Set.elements world);
  let env = E.create (PT_Set.elements world) in
  (* On ajoute toute les logics et type et donc même celle qui sont builtin *)
  let env = Env.fold_type (fun id sch env -> E.add_type env id sch) env in
  if Options.monoinstoutput_world then output_world world env;
  let env = Env.fold_global_logic (fun id sch env -> 
                                     try
                                       E.add_logic env id sch
                                     with e -> 
                                  if debug then 
                                    Format.eprintf "error in logic : %a,%a@." Ident.print id 
                                      Util.print_logic_type sch.Env.scheme_type;
                                       raise e) env in
  if debug then Format.eprintf "env : %a" E.print env;
  (* first the prelude *)
  List.iter f (prelude env);
  (* then the queue *)
  ignore (List.fold_left (fun env x -> (translate_assertion env f x)) env decls);
  ()

let reset () = Queue.clear queue
