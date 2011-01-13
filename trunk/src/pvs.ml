(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
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



open Logic
open Logic_decl
open Types
open Cc
open Misc
open Util
open Ident
open Env
open Format
open Vcg
open Pp


let infix_table = ref Idmap.empty

let () =
  List.iter (fun (id,s) -> infix_table := Idmap.add id s !infix_table)
    [ t_lt, "<" ;
      t_le, "<=";
      t_gt, ">";
      t_ge, ">=";
      t_eq, "=";
      t_neq, "/=";
      t_bool_and, "AND";
      t_bool_or, "OR";
      t_bool_xor, "/=" ;
      t_gt_int_bool, ">";
      t_gt_real_bool, ">";
      t_ge_int_bool, ">=";
      t_ge_real_bool, ">=";
      t_le_int_bool, "<=";
      t_le_real_bool, "<=";
      t_lt_int_bool, "<";
      t_lt_real_bool, "<";
      t_eq_int_bool, "=";
      t_eq_real_bool, "=";
      t_neq_int_bool, "/=";
      t_neq_real_bool, "/=";
      t_lt_int, "<" ;
      t_le_int, "<=";
      t_gt_int, ">";
      t_ge_int, ">=";
      t_eq_int, "=";
      t_neq_int, "/=";
      t_lt_real, "<" ;
      t_le_real, "<=";
      t_gt_real, ">";
      t_ge_real, ">=";
      t_eq_real, "=";
      t_neq_real, "/=";
    ]

let is_infix id = Idmap.mem id !infix_table
	
let infix id = 
  try
    Idmap.find id !infix_table
  with Not_found -> assert false



let prefix_table = ref Idmap.empty

let () =
  List.iter (fun (id,s) -> prefix_table := Idmap.add id s !prefix_table)
    [ t_abs_real, "abs";
      t_real_max, "max";
      t_real_min, "min";
      t_sqrt_real, "sqrt";
    ]

let is_prefix id = Idmap.mem id !prefix_table
	
let prefix id = 
  try
    Idmap.find id !prefix_table
  with Not_found -> assert false


let is_pvs_keyword =
  let ht = Hashtbl.create 50  in
  List.iter (fun kw -> Hashtbl.add ht kw ()) 
    [];
  Hashtbl.mem ht

let leading_underscore s = s <> "" && s.[0] = '_'

let idents fmt s = 
  (* PVS does not expect names to begin with an underscore. *)
  if is_pvs_keyword s || leading_underscore s then
    fprintf fmt "why__%s" s
  else 
    fprintf fmt "%s" s

let ident fmt id = idents fmt (Ident.string id)

let rec filter_phantom_type = function
  | PTexternal (_, id) ->
      not (Hashtbl.mem Options.phantom_types (Ident.string id))
  | PTvar { type_val = Some t} -> filter_phantom_type t   
  | _ -> true

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTreal -> fprintf fmt "real"
  | PTexternal ([pt], id) when id == farray -> 
      fprintf fmt "warray[%a]" print_pure_type pt
  | PTvar { type_val = Some t} -> fprintf fmt "%a" print_pure_type t      
  | PTvar v -> fprintf fmt "A%d" v.tag
  | PTexternal (i, id) -> 
      fprintf fmt "%a%a" ident id print_instance i

and print_instance fmt l = 
  match List.filter filter_phantom_type l with
    | [] -> ()
    | i -> fprintf fmt "[%a]" (print_list comma print_pure_type) i

let print_real = Print_real.print_no_exponent 

let print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a;b], _) when is_infix id ->
	fprintf fmt "@[<hov 2>(%a %s@ %a)@]" print1 a (infix id) print1 b
    | t -> 
	print1 fmt t
  and print1 fmt = function
    | Tapp (id, [a;b], _) when id == t_add_int || id == t_sub_int ->
	fprintf fmt "@[<hov 2>%a %s@ %a@]" 
	  print1 a (if id == t_add_int then "+" else "-") print2 b
    | Tapp (id, [a;b], _) when id == t_add_real || id == t_sub_real ->
	fprintf fmt "@[<hov 2>%a %s@ %a@]" 
	  print1 a (if id == t_add_real then "+" else "-") print2 b
    | t ->
	print2 fmt t
  and print2 fmt = function
    | Tapp (id, [a;b], _) when id == t_mul_int || id == t_mul_real ->
	fprintf fmt "@[<hov 2>%a *@ %a@]" print2 a print3 b
    | Tapp (id, [a;b], _) when id == t_div_real ->
	fprintf fmt "@[<hov 2>%a /@ %a@]" print2 a print3 b
(*
    | Tapp (id, [a;b], _) when id == t_div_int ->
	fprintf fmt "(@[div(%a,%a)@])" print0 a print0 b
    | Tapp (id, [a;b], _) when id == t_mod_int ->
	fprintf fmt "(@[mod(%a,%a)@])" print0 a print0 b
*)
    | t ->
	print3 fmt t
  and print3 fmt = function
    | Tconst (ConstInt n) -> 
	fprintf fmt "%s" n
    | Tconst (ConstBool b) -> 
	fprintf fmt "%b" b
    | Tconst ConstUnit -> 
	fprintf fmt "unit" 
    | Tconst (ConstFloat f) -> 
	print_real fmt ~prefix_div:false f
    | Tapp (id, [t], _) when id == t_real_of_int ->
	fprintf fmt "%a" print3 t
    | Tderef _ ->
	assert false
    | Tvar id when id == implicit ->
	assert false
    | Tvar id when id == t_zwf_zero ->
	fprintf fmt "zwf_zero"
    | Tvar id ->
	ident fmt id
    | Tapp (id, [a; Tapp (id', [b], _)], _) 
      when id == t_pow_real && id' == t_real_of_int ->
	fprintf fmt "(@[%a@ ^ %a@])" print3 a print3 b
    | Tapp (id, [a;b], _) when id == t_pow_real ->
	fprintf fmt "(@[%a@ ^ %a@])" print3 a print3 b
    | Tapp (id, tl, i) when is_prefix id -> 
	fprintf fmt "%s%a(@[%a@])" 
	  (prefix id) print_instance (List.rev i) (print_list comma print0) tl
    | Tapp (id, [t], _) when id == t_neg_int || id == t_neg_real ->
	fprintf fmt "-%a" print3 t
    | Tapp (id, [t], _) when id == t_bool_not ->
	fprintf fmt "(NOT(%a))" print3 t
    | Tapp (id, [a; b; c], _) when id == if_then_else -> 
	fprintf fmt "(@[IF %a@ THEN %a@ ELSE %a@ ENDIF@])" print0 a print0 b print0 c
    | Tapp (id, _l, _) as t when is_infix id ->
	fprintf fmt "@[%a@]" print0 t
    | Tapp (id, _l, _) as t when is_arith_binop id ->
	fprintf fmt "@[(%a)@]" print0 t
    | Tapp (id, [], i) -> 
	fprintf fmt "%a%a" ident id print_instance (List.rev i)
    | Tapp (id, tl, i) -> 
	fprintf fmt "%a%a(@[%a@])" 
	  ident id print_instance (List.rev i) (print_list comma print0) tl
    | Tnamed(_lab,t) -> print3 fmt t
  in
  print0 fmt t

let print_logic_binder fmt (id,pt) =
  fprintf fmt "%a:%a" ident id print_pure_type pt


let print_predicate fmt p =
  let rec print0 fmt = function
    | Pif (a, b, c) -> 
	fprintf fmt "@[IF "; print_term fmt a; fprintf fmt "@ THEN ";
	print0 fmt b; fprintf fmt "@ ELSE "; print0 fmt c; 
	fprintf fmt " ENDIF@]"
    | Pimplies (_, a, b) -> 
	fprintf fmt "@[("; print1 fmt a; fprintf fmt " IMPLIES@ "; 
	print0 fmt b; fprintf fmt ")@]"
    | Piff (a, b) -> 
	fprintf fmt "@[("; print1 fmt a; fprintf fmt " IFF@ "; 
	print0 fmt b; fprintf fmt ")@]"
    | p -> print1 fmt p
  and print1 fmt = function
    | Por (a, b) -> print1 fmt a; fprintf fmt " OR@ "; print2 fmt b
    | p -> print2 fmt p
  and print2 fmt = function
    | Pand (_, _, a, b) | Forallb (_, a, b) -> 
        print2 fmt a; fprintf fmt " AND@ "; print3 fmt b
    | p -> print3 fmt p
  and print3 fmt = function
    | Ptrue ->
	fprintf fmt "True"
    | Pvar id when id == default_post ->
	fprintf fmt "True"
    | Pfalse ->
	fprintf fmt "False"
    | Pvar id -> 
	ident fmt id
    | Papp (id, tl, _) when id == t_distinct ->
	fprintf fmt "@[(%a)@]" print0 (Util.distinct tl)
    | Papp (id, [t], _) when id == well_founded ->
	fprintf fmt "well_founded?(%a)" print_term t
    | Papp (id, [a;b], _) when id == t_zwf_zero ->
	fprintf fmt "zwf_zero(%a, %a)" print_term a print_term b
    | Papp (id, [a;b], _) when is_int_comparison id || is_real_comparison id ->
	fprintf fmt "@[%a %s@ %a@]" 
	  print_term a (infix id) print_term b
    | Papp (id, [a;b], _) when is_eq id ->
	fprintf fmt "@[%a =@ %a@]" print_term a print_term b
    | Papp (id, [a;b], _) when is_neq id ->
	fprintf fmt "%a /=@ %a" print_term a print_term b
    | Papp (id, l, i) -> 	
	fprintf fmt "%a%a(@[" ident id print_instance (List.rev i);
	print_list (fun fmt () -> fprintf fmt ",@ ") print_term fmt l;
	fprintf fmt "@])"
    | Pnot p -> 
	fprintf fmt "NOT "; print3 fmt p
    | Forall (_,id,n,t,_,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "@[(FORALL (%a: " ident id';
	print_pure_type fmt t; fprintf fmt "):@ ";
	print0 fmt p'; fprintf fmt ")@]"
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[EXISTS (%a: " ident id';
	print_pure_type fmt t; fprintf fmt "):@ ";
	print0 fmt p'; fprintf fmt "@])"
    | Pnamed (_, p) -> (* TODO: print name *)
	print3 fmt p
    | Plet (_, n, _, t, p) ->
	print3 fmt (subst_term_in_predicate n t p)
    | (Por _ | Piff _ | Pand _ | Pif _ | Pimplies _ | Forallb _) as p -> 
	fprintf fmt "(%a)" print0 p
  in
  print0 fmt p

let print_sequent fmt (hyps,concl) =
  let rec print_seq = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "FORALL (%a: %a) :@\n" ident id print_pure_type v;
	print_seq hyps
    | Spred (_,p) :: hyps -> 
	print_predicate fmt p; fprintf fmt " IMPLIES@\n";
	print_seq hyps
  in
  print_seq hyps

let last_theory = ref None

let import_last_theory fmt = match !last_theory with
  | None -> ()
  | Some t -> fprintf fmt "  IMPORTING %s@\n@\n" t

let begin_theory fmt th =
  fprintf fmt "%s: THEORY@\nBEGIN@\n@\n" th;
  fprintf fmt "  %s@\n" Options.pvs_preamble;
  import_last_theory fmt

let begin_sub_theory fmt n th =
  fprintf fmt "%s" th;
  if n > 0 then begin
    fprintf fmt "[";
    for i = 1 to n do fprintf fmt "A%d" i; if i < n then fprintf fmt "," done;
    fprintf fmt ": TYPE]"
  end;
  fprintf fmt ": THEORY@\nBEGIN@\n@\n";
  fprintf fmt "  %s@\n" Options.pvs_preamble;
  import_last_theory fmt
    
let end_theory fmt th =
  fprintf fmt "END %s@\n@\n" th

let print_logic_type fmt = function
  | Predicate [] ->
      fprintf fmt "bool"
  | Predicate pl -> 
      fprintf fmt "[%a -> bool]"
	(print_list comma print_pure_type) pl
  | Function ([], pt) ->
      print_pure_type fmt pt
  | Function (pl, t) -> 
      fprintf fmt "[%a -> %a]"
	(print_list comma print_pure_type) pl print_pure_type t

let declare_type fmt id = 
  fprintf fmt "  @[%a: TYPE+;@]@\n@\n" idents id

let declare_alg_type fmt id cs =
  let print_cargs c fmt pl =
    let cpt = ref 0 in
    let print_carg fmt t =
      incr cpt; fprintf fmt "%s_proj_%i : %a" c !cpt print_pure_type t
    in
    match pl with
    | [] -> ()
    | _  -> fprintf fmt "@[(%a)@]" (print_list comma print_carg) pl
  in
  let cons fmt (c,pl) =
    let c = Ident.string c in
    fprintf fmt "%s%a : %s?" c (print_cargs c) pl c
  in
  fprintf fmt "  @[<hov 2>%s: DATATYPE@\n@[<hov 2>BEGIN@\n%a@]@\nEND %s@]@\n@\n"
    id (print_list newline cons) cs id

let print_logic fmt id t = 
  fprintf fmt "  %%%% Why logic %s@\n" id;
  fprintf fmt "  %a: @[%a@]@\n@\n" idents id print_logic_type t
    
let print_axiom fmt id p =
  fprintf fmt "  @[%%%% Why axiom %s@]@\n" id;
  fprintf fmt "  @[<hov 2>%a: AXIOM@ @[%a@]@]@\n@\n" idents id print_predicate p
    
let print_predicate_def fmt id (bl,p) =
  fprintf fmt "  @[<hov 2>%a(@[%a@]) : bool =@ @[%a@]@]@\n@\n"
    ident id (print_list comma print_logic_binder) bl print_predicate p
    
let print_inductive_def fmt id inddef =
  let (_vars,(bl,cases)) = Env.specialize_inductive_def inddef in
  let newvars = List.map (fun t -> (fresh_var(),t)) bl in
  let body = PredDefExpansor.inductive_inverse_body id newvars cases in
  fprintf fmt "  @[<hov 2>INDUCTIVE %a(@[%a@]) : bool =@ @[%a@]@]@\n@\n"
    ident id (print_list comma print_logic_binder) newvars print_predicate body
    
let print_function_def fmt id (bl,t,e) =
  fprintf fmt "  @[<hov 2>%a(@[%a@]) : %a =@ @[%a@]@]@\n@\n"
    ident id (print_list comma print_logic_binder) bl 
    print_pure_type t print_term e
    
let print_obligation fmt (loc,_expl,id,s) =
  fprintf fmt "  @[%% %a @]@\n" (Loc.report_obligation_position ~onlybasename:true) loc;
  fprintf fmt "  @[<hov 2>%a: LEMMA@\n" idents id;
  print_sequent fmt s;
  fprintf fmt "@]@\n@\n"
  (*;
  fprintf fmt "@[%% %a @]@\n@\n" Util.print_explanation expl
  *)

(* polymorphism *)

let print_scheme l =
  let r = ref 0 in
  Env.Vmap.iter
    (fun _ x -> 
       incr r;
       x.type_val <- Some (PTvar { tag = !r; user = false; type_val = None }))
    l

let tvar_so_far = ref 0

let print_goal fmt (loc, expl, id, s) =
  let n = Vset.cardinal s.scheme_vars in
  if n > !tvar_so_far then begin
    fprintf fmt "  ";
    for i = !tvar_so_far + 1 to n do
      fprintf fmt "A%d" i; if i < n then fprintf fmt ", "
    done;
    fprintf fmt ": TYPE+;@\n@\n";
    tvar_so_far := n
  end;
  let l,s = Env.specialize_sequent s in
  print_scheme l;
  print_obligation fmt (loc,expl,id,s)

let print_logic_scheme fmt id s =
  let l,t = Env.specialize_logic_type s in
  print_scheme l;
  print_logic fmt id t

let print_axiom_scheme fmt id s =
  let l,a = Env.specialize_predicate s in
  print_scheme l;
  print_axiom fmt id a

type def =
  | DefFunction of function_def scheme
  | DefPredicate of predicate_def scheme
  | DefInductive of inductive_def scheme

let print_def_scheme fmt id = function
  | DefFunction s -> 
      let l,d = Env.specialize_function_def s in
      print_scheme l;
      print_function_def fmt id d
  | DefPredicate s ->
      let l,d = Env.specialize_predicate_def s in
      print_scheme l;
      print_predicate_def fmt id d
  | DefInductive s ->
      let l,_d = Env.specialize_inductive_def s in
      print_scheme l;      
      print_inductive_def fmt id s

let queue = Queue.create ()

let push_decl d = Queue.add d queue

let iter f = Queue.iter f queue

let reset () = Queue.clear queue

let output_elem fmt = function
  | Dtype (_loc, id, []) -> declare_type fmt (Ident.string id)
  | Dtype _ -> assert false
  | Dalgtype [(_loc, id, {scheme_type=([],cs)})] ->
      declare_alg_type fmt (Ident.string id) cs
  | Dalgtype _ -> assert false
  | Dlogic (_loc, id, t) -> print_logic fmt (Ident.string id) t.scheme_type
  | Dpredicate_def (_loc, id, d) -> print_predicate_def fmt id d.scheme_type
  | Dinductive_def(_loc, ident, inddef) -> print_inductive_def fmt ident inddef
  | Dfunction_def (_loc, id, d) -> print_function_def fmt id d.scheme_type
  | Daxiom (_loc, id, p) -> print_axiom fmt id p.scheme_type
  | Dgoal (loc, expl, id, s) -> print_goal fmt (loc, expl, id, s)

module ArMap = struct

  module S = Set.Make(struct type t = int let compare = compare end)

  type 'a t = { mutable keys : S.t; vals : (int, 'a Queue.t) Hashtbl.t }

  let create () = { keys = S.empty; vals = Hashtbl.create 17 }

  let add n x m =
    try 
      Queue.add x (Hashtbl.find m.vals n)
    with Not_found -> 
      let q = Queue.create () in 
      Queue.add x q;
      Hashtbl.add m.vals n q; 
      m.keys <- S.add n m.keys

  let add_scheme s = add (Vset.cardinal s.scheme_vars)

  let importing fmt s m =
    let one fmt n = fprintf fmt "%s%d" s n in
    if not (S.is_empty m.keys) then
      fprintf fmt "  @[<hov 2>IMPORTING %a@]@\n@\n" 
	(print_list comma one) (S.elements m.keys)

  let iter f m = Hashtbl.iter f m.vals

  let print_theories fmt prefix preamble f m =
    Hashtbl.iter
      (fun n q -> 
	let tn = prefix ^ string_of_int n in
	begin_sub_theory fmt n tn;
	preamble ();
	Queue.iter f q;
	end_theory fmt tn) 
      m.vals

end

type pvs_theories = {
  types : (string list * string * (Ident.t * pure_type list) list) ArMap.t;
  decls : (string * logic_type scheme) ArMap.t;
  defs : (string * def) Queue.t;
  axioms : (string * predicate scheme) ArMap.t;
  goals : (loc * Logic_decl.vc_expl * string * sequent scheme) Queue.t;
  mutable poly : bool;
}

let sort_theory () =
  let th = 
    { types = ArMap.create ();
      decls = ArMap.create ();
      defs = Queue.create ();
      axioms = ArMap.create ();
      goals = Queue.create ();
      poly = false }
  in
  let poly s = if not (Vset.is_empty s.scheme_vars) then th.poly <- true in
  let sort = function
    | Dtype (_, id, l) ->
	let n = List.length l in
	if n > 0 then th.poly <- true;
        ArMap.add n (l, Ident.string id, []) th.types
    | Dalgtype [(_, id, { scheme_type = ([], cs) })] ->
        ArMap.add 0 ([], Ident.string id, cs) th.types
    | Dalgtype _ ->
        failwith "PVS: polymorphic algebraic datatypes are not supported"
    | Dlogic (_, id, s) -> 
	poly s; ArMap.add_scheme s (Ident.string id, s) th.decls
    | Dpredicate_def (_, id, s) -> 
	poly s; Queue.add (Ident.string id, DefPredicate s) th.defs
    | Dinductive_def(_loc, ident, inddef) ->
	poly inddef; Queue.add (Ident.string ident, DefInductive inddef) th.defs
    | Dfunction_def (_, id, s) -> 
	poly s; Queue.add (Ident.string id, DefFunction s) th.defs
    | Daxiom (_, id, s) -> 
	poly s; ArMap.add_scheme s (id,s) th.axioms
    | Dgoal (loc, expl, id, s) -> 
	Queue.add (loc,expl,id,s) th.goals
  in
  Queue.iter sort queue;
  th

let output_theory fmt th_name =
  tvar_so_far := 0;
  let th = sort_theory () in
  if th.poly then begin
    (* complex case: there are some polymorphic elements -> several theories *)
    let import_types () = ArMap.importing fmt (th_name ^ "_types") th.types in
    let import_decls () = ArMap.importing fmt (th_name ^ "_decls") th.decls in
    let importing l = 
      if l <> [] then 
	fprintf fmt "  @[<hov 2>IMPORTING %a@]@\n@\n" 
	  (print_list comma pp_print_string) l
    in
    let all_defs = 
      Queue.fold (fun l (id,_) -> (th_name ^ "_" ^ id) :: l) [] th.defs
    in
    let import_defs () = importing all_defs in
    let import_axioms () = ArMap.importing fmt (th_name^"_axioms") th.axioms in
    import_types ();
    import_decls ();
    import_defs ();
    import_axioms ();
    (* goals *)
    Queue.iter (print_goal fmt) th.goals;
    end_theory fmt th_name;
    (* axioms *)
    ArMap.print_theories fmt (th_name ^ "_axioms") 
      (fun () -> import_types (); import_decls (); import_defs ())
      (fun (id,a) -> print_axiom_scheme fmt id a) th.axioms;
    (* defs *)
    let defs_so_far = ref [] in
    Queue.iter 
      (fun (id,def) -> 
	let n = 
	  let vars = match def with 
	    | DefFunction s -> s.scheme_vars
	    | DefInductive s -> s.scheme_vars
	    | DefPredicate s -> s.scheme_vars
	  in
	  Vset.cardinal vars
	in
	let name = th_name ^ "_" ^ id in
	begin_sub_theory fmt n name;
	import_types ();
	import_decls ();
	importing !defs_so_far;
	print_def_scheme fmt (Ident.create id) def;
	end_theory fmt name;
        defs_so_far := name :: !defs_so_far)
      th.defs;
    (* decls *)
    ArMap.print_theories fmt (th_name ^ "_decls") 
      import_types
      (fun (id,t) -> print_logic_scheme fmt id t) th.decls;
    (* types *)
    ArMap.print_theories fmt (th_name ^ "_types") 
      (fun () -> ())
      (function
        | (_,id,[]) -> declare_type fmt id
        | (_,id,cs) -> declare_alg_type fmt id cs) th.types
  end else begin 
    (* simple case: no polymorphism at all -> a single theory *)
    iter (output_elem fmt);
    end_theory fmt th_name
  end

let output_file fwe =
  let sep = "  %% DO NOT EDIT BELOW THIS LINE" in
  let file = fwe ^ "_why.pvs" in
  let th_name = (Filename.basename fwe) ^ "_why" in
  do_not_edit_below ~file
    ~before:(fun fmt -> begin_theory fmt th_name)
    ~sep
    ~after:(fun fmt -> output_theory fmt th_name);
  last_theory := Some th_name
    

