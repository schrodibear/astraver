(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: effect.ml,v 1.8 2002-03-13 16:15:46 filliatr Exp $ i*)

(*s Effects. *)

open Ident
open Misc

(*s An effect is composed of two lists [(r,w)] of variables.
    The first one is the list of all variables (the input)
    and the second one is the list of possibly modified variables (the output)
 
    INVARIANTS: 
    1. there are no duplicate elements in each list 
    2. output is contained in input

    REMARK: for most operations, sets will be more relevant than lists,
    but order must not change when a substitution is applied and thus
    lists are preferred *)

type t = Ident.t list * Ident.t list

(*s the empty effect *)

let bottom = ([], [])

(*s basic operations *)

let list_add x l = if List.mem x l then l else x :: l

let list_remove x l = 
  let rec rem_rec = function
    | [] -> []
    | y :: l -> if x = y then l else y :: rem_rec l
  in
  if List.mem x l then rem_rec l else l

let mem x (r,w) = (List.mem x r) || (List.mem x w)

(* [list_union] is a merge sort *)
let list_union l1 l2 = 
  let rec basic_union = function
    | [], s2 -> s2
    | s1, [] -> s1
    | ((v1 :: l1) as s1), ((v2 :: l2) as s2) ->
	if v1 < v2 then
	  v1 :: basic_union (l1,s2)
	else if v1 > v2 then
	  v2 :: basic_union (s1,l2)
	else
	  v1 :: basic_union (l1,l2)
  in
  basic_union (List.sort compare l1, List.sort compare l2)

(*s adds reads and writes variables *)

let add_read x ((r,w) as e) = (list_add x r, w)

let add_reads ids = Ident.Idset.fold add_read ids

let add_write x (r,w) = (list_add x r, list_add x w)

(*s access *)

let get_reads = fst
let get_writes = snd
let get_repr e = e

(*s tests *)

let is_read  (r,_) id = List.mem id r
let is_write (_,w) id = List.mem id w

(*s union and disjunction *)

let union (r1,w1) (r2,w2) = (list_union r1 r2, list_union w1 w2)

(*s comparison relation *)

let le e1 e2 = failwith "effects: le: not yet implemented"

let inf e1 e2 = failwith "effects: inf: not yet implemented"

(*s remove *)

let remove x (r,w) = (list_remove x r, list_remove x w)

(*s occurrence *)

let occur x (r,w) = List.mem x r || List.mem x w

(*s substitution *)

let list_subst (x,x') l =
  let rec subst = function
    | [] -> []
    | y :: r -> if y = x then x' :: r else y :: subst r
  in
  if List.mem x l then subst l else l

let subst_one s (r,w) = (list_subst s r, list_subst s w)

let subst = List.fold_right subst_one

(*s pretty-print *)

open Format

let print fmt (r,w) =
  fprintf fmt "@[";
  if r <> [] then begin
    fprintf fmt "reads ";
    print_list (fun fmt () -> fprintf fmt ",@ ") Ident.print fmt r;
    fprintf fmt "@ ";
  end;
  if w <> [] then begin
    fprintf fmt "writes ";
    print_list (fun fmt () -> fprintf fmt ",@ ") Ident.print fmt w;
    fprintf fmt "@ ";
  end;
  fprintf fmt "@]"

