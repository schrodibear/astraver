
open Format
open Cast
open Creport
open Info

(* Type equality (i.e. structural equality, but ignoring attributes) *)
(* TODO: pointers = arrays *)

let rec eq_type ty1 ty2 = 
  eq_type_node ty1.ctype_node ty2.ctype_node

and eq_type_node tn1 tn2 = match tn1, tn2 with
  | CTvoid, CTvoid
  | CTint _, CTint _ 
  | CTfloat _, CTfloat _ ->
      true
  | CTvar x1, CTvar x2 ->
      x1 = x2
  | CTarray (ty1, _), CTarray (ty2, _) ->
      eq_type ty1 ty2 (* TODO: taille? *)
  | CTpointer ty1, CTpointer ty2 ->
      eq_type ty1 ty2
  | CTstruct (s1, _), CTstruct (s2, _) ->
      s1 = s2
  | CTstruct_named _, _ | _, CTstruct_named _ ->
      assert false
  | CTunion (u1, _), CTunion (u2, _) ->
      u1 = u2
  | CTunion_named _, _ | _, CTunion_named _ ->
      assert false
  | CTenum (e1, _), CTenum (e2, _) ->
      e1 = e2
  | CTenum_named _, _ | _, CTenum_named _ ->
      assert false
  | CTfun (pl1, ty1), CTfun (pl2, ty2) ->
      eq_type ty1 ty2 &&
      (try List.for_all2 (fun (ty1,_) (ty2,_) -> eq_type ty1 ty2) pl1 pl2
       with Invalid_argument _ -> false)
  | _ ->
      false

(* [sub_type ty1 ty2] is true if type [ty1] can be coerced
   to type [ty2] (with function [coerce] below) *)

let sub_type ty1 ty2 = match ty1.ctype_node, ty2.ctype_node with
  | CTint _, CTfloat _ -> true
  | CTpointer { ctype_node = CTvoid }, CTpointer _ -> true
  | _ -> eq_type ty1 ty2

let compatible ty1 ty2 = sub_type ty1 ty2 || sub_type ty2 ty1

let arith_type ty = match ty.ctype_node with
  | CTint _ | CTfloat _ -> true
  | _ -> false

let pointer_type ty = match ty.ctype_node with
  | CTpointer _ -> true
  | _ -> false

let is_null e = match e.texpr_node with
  | TEconstant s -> (try int_of_string s = 0 with _ -> false)
  | _ -> false

(*s Global environment *)

(* tagged types *)
let (tags_t : (string, texpr ctype) Hashtbl.t) = Hashtbl.create 97

let clash_tag l s1 s2 = 
  let redef t n = error l (sprintf "redeclaration of `%s %s'" t n) in
  match s1.ctype_node, s2.ctype_node with
  | CTstruct (n,_), CTstruct _ -> redef "struct" n
  | CTunion (n,_), CTunion _ -> redef "union" n
  | CTenum (n,_), CTenum _ -> redef "enum" n
  | (CTstruct (n,_) | CTunion (n,_) | CTenum (n,_)), 
    (CTstruct _ | CTunion _ | CTenum _) -> 
      error l (sprintf "`%s' defined as wrong kind of tag" n)
  | _ -> assert false

let is_tag_type = Hashtbl.mem tags_t

let find_tag_type = Hashtbl.find tags_t

let add_tag_type l x s = 
  if is_tag_type x then clash_tag l s (find_tag_type x);
  Hashtbl.add tags_t x s

(* typedefs *)

let typedef_t = (Hashtbl.create 97 : (string, tctype) Hashtbl.t)

let is_typedef = Hashtbl.mem typedef_t

let find_typedef = Hashtbl.find typedef_t

let add_typedef l x ty = 
  if is_typedef x then begin
    if ty = find_typedef x then error l ("redefinition of `" ^ x ^ "'")
    else error l ("conflicting types for `" ^ x ^ "'")
  end else
    Hashtbl.add typedef_t x ty

(* variables and functions *)
let (sym_t : (string, (texpr ctype * var_info)) Hashtbl.t) = Hashtbl.create 97

let is_sym = Hashtbl.mem sym_t

let find_sym = Hashtbl.find sym_t

let add_sym l x ty = 
  if is_sym x then begin
    let (t,i) = find_sym x in
    if not (eq_type t ty) then 
      (* TODO accepter fonctions avec arguments si aucun la première fois 
	 Question de Claude: accepter aussi un raffinement des specs ? *)
      error l ("conflicting types for " ^ x)
  end else
    Hashtbl.add sym_t x (ty,default_var_info x)

(*s Environments for the logical side *)

let functions = 
  (Hashtbl.create 97 : (string, tctype list * tctype) Hashtbl.t)
let add_fun = Hashtbl.add functions
let find_fun = Hashtbl.find functions

let predicates = (Hashtbl.create 97 : (string, tctype list) Hashtbl.t) 
let add_pred = Hashtbl.add predicates
let find_pred = Hashtbl.find predicates

(*s Environments for local variables and local structs/unions/enums *)

module Env = struct

  module M = Map.Make(String)

  type t = { 
    vars : (texpr ctype * var_info) M.t; 
    tags : texpr ctype M.t;
  }

  let empty = { vars = M.empty; tags = M.empty }

  let add x t info env = 
    { env with vars = M.add x (t,info) env.vars }

  let find x env = M.find x env.vars

  (* add a local tagged type *)
  let add_tag_type l x s env = 
    if M.mem x env.tags then clash_tag l s (M.find x env.tags);
    { env with tags = M.add x s env.tags }

  (* look for a tagged type first in locals then in globals *)
  let find_tag_type x env = 
    try M.find x env.tags with Not_found -> find_tag_type x

end

