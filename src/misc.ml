(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: misc.ml,v 1.5 2001-08-24 19:00:07 filliatr Exp $ i*)

open Ident
open Logic
open Types 

(*s debug *)

let debug = ref false

(*s Utility functions. *)

let map_succeed f = 
  let rec map_f = function 
    | [] -> []
    |  h::t -> try (let x = f h in x :: map_f t) with Failure _ -> map_f t
  in 
  map_f 

let option_app f = function None -> None | Some x -> Some (f x)

let list_of_some = function None -> [] | Some x -> [x]

let difference l1 l2 =
  let rec diff = function
    | [] -> []
    | a::rem -> if List.mem a l2 then diff rem else a::(diff rem)
  in
  diff l1

(*s Functions on names *)

type avoid = Ident.set

let renaming_of_ids avoid ids =
  let rec rename avoid = function
    | [] -> 
	[], avoid
    | x::rem ->
	let al,avoid = rename avoid rem in
	let x' = Ident.next_away x avoid in
	(x,x')::al, Idset.add x' avoid
  in
  rename avoid ids

(*s hypotheses names *)

let next s r = function
  | Anonymous -> incr r; Ident.create (s ^ string_of_int !r)
  | Name id -> id

let reset_names,pre_name,post_name,inv_name,
    test_name,bool_name,var_name,phi_name,for_name,label_name =
  let pre = ref 0 in
  let post = ref 0 in
  let inv = ref 0 in
  let test = ref 0 in
  let bool = ref 0 in
  let var = ref 0 in
  let phi = ref 0 in
  let forr = ref 0 in
  let label = ref 0 in
    (fun () -> 
       pre := 0; post := 0; inv := 0; test := 0; 
       bool := 0; var := 0; phi := 0; label := 0),
    (next "Pre" pre),
    (next "Post" post),
    (next "Inv" inv),
    (next "Test" test),
    (fun () -> next "Bool" bool Anonymous),
    (next "Variant" var),
    (fun () -> next "rphi" phi Anonymous),
    (fun () -> next "for" forr Anonymous),
    (fun () -> Ident.string (next "Label" label Anonymous))

let id_of_name = function Name id -> id | Anonymous -> default

let warning s = Format.eprintf "warning: %s\n" s

(*s Functions on terms and predicates. *)

let applist f l = match (f,l) with
  | f, [] -> f
  | Tvar id, l -> Tapp (id, l)
  | Tapp (id, l), l' -> Tapp (id, l @ l')
  | (Tbound _ | Tconst _), _ -> assert false

let rec collect_term s = function
  | Tvar id -> Idset.add id s
  | Tapp (_, l) -> List.fold_left collect_term s l
  | Tconst _ | Tbound _ -> s

and collect_pred s = function
  | Pterm t -> collect_term s t
  | Pimplies (a, b) | Pand (a, b) | Por (a, b) -> 
      collect_pred (collect_pred s a) b
  | Pif (a, b, c) -> collect_pred (collect_pred (collect_pred s a) b) c
  | Pnot a -> collect_pred s a
  | Forall (_, _, _, p) -> collect_pred s p

let term_vars = collect_term Idset.empty
let predicate_vars = collect_pred Idset.empty

let rec tsubst_in_term alist = function
  | Tvar x as t -> (try List.assoc x alist with Not_found -> t)
  | Tapp (x,l) -> Tapp (x, List.map (tsubst_in_term alist) l)
  | Tconst _ | Tbound _ as t -> t

let rec map_predicate f = function
  | Pimplies (a, b) -> Pimplies (f a, f b)
  | Pif (a, b, c) -> Pif (f a, f b, f c)
  | Pand (a, b) -> Pand (f a, f b)
  | Por (a, b) -> Por (f a, f b)
  | Pnot a -> Pnot (f a)
  | Forall (id, b, v, p) -> Forall (id, b, v, f p)
  | Pterm _ as p -> p

let rec tsubst_in_predicate alist = function
  | Pterm t -> Pterm (tsubst_in_term alist t)
  | p -> map_predicate (tsubst_in_predicate alist) p

let subst_in_term alist = 
  tsubst_in_term (List.map (fun (id,id') -> (id, Tvar id')) alist)
let subst_in_predicate alist = 
  tsubst_in_predicate (List.map (fun (id,id') -> (id, Tvar id')) alist)

let rec bsubst_in_term alist = function
  | Tbound n as t -> (try List.assoc n alist with Not_found -> t)
  | Tapp (x,l) -> Tapp (x, List.map (bsubst_in_term alist) l)
  | Tconst _ | Tvar _ as t -> t

let rec bsubst_in_predicate alist = function
  | Pterm t -> Pterm (bsubst_in_term alist t)
  | p -> map_predicate (bsubst_in_predicate alist) p

let equals_true = function
  | Tapp (id, _) as t when is_relation id -> t
  | t -> Tapp (t_eq, [t; Tconst (ConstBool true)])

let negate id =
  if id == t_lt then t_ge
  else if id == t_le then t_gt 
  else if id == t_gt then t_le
  else if id == t_ge then t_lt
  else if id == t_eq then t_noteq
  else if id == t_noteq then t_eq
  else assert false

let equals_false = function
  | Tapp (id, l) when is_relation id -> Tapp (negate id, l)
  | t -> Tapp (t_eq, [t; Tconst (ConstBool false)])

let rec mlize_type = function
  | PureType pt -> pt
  | Ref v -> mlize_type v
  | Array (s, v) -> PTarray (s, mlize_type v)
  | Arrow _ -> assert false

let rec occur_term id = function
  | Tvar id' -> id = id'
  | Tapp (_, l) -> List.exists (occur_term id) l
  | Tconst _ | Tbound _ -> false

let rec occur_predicate id = function
  | Pterm t -> occur_term id t
  | Pif (a, b, c) -> 
      occur_predicate id a || occur_predicate id b || occur_predicate id c
  | Pimplies (a, b) -> occur_predicate id a || occur_predicate id b
  | Pand (a, b) -> occur_predicate id a || occur_predicate id b
  | Por (a, b) -> occur_predicate id a || occur_predicate id b
  | Pnot a -> occur_predicate id a
  | Forall (_,_,_,a) -> occur_predicate id a
  
(*s Smart constructors. *)

let ttrue = Tconst (ConstBool true)
let tfalse = Tconst (ConstBool false)
let ptrue = Pterm ttrue
let pfalse = Pterm tfalse

let pif a b c =
  if a = ptrue then b else if a = pfalse then c else Pif (a, b ,c)

let pand a b = 
  if a = ptrue then b else if b = ptrue then a else
  if a = pfalse || b = pfalse then pfalse else
  Pand (a, b)

let por a b =
  if a = ptrue || b = ptrue then ptrue else
  if a = pfalse then b else if b = pfalse then a else
  Por (a, b)

let pnot a =
  if a = ptrue then pfalse else if a = pfalse then ptrue else Pnot a

(*s Pretty-print *)

open Format

let rec print_list fmt sep print = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list fmt sep print r

let comma fmt () = fprintf fmt ",@ "
let nothing fmt () = ()

let hov n fmt f x = pp_open_hovbox fmt n; f x; pp_close_box fmt ()

let rec print_term fmt = function
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "unit" 
  | Tconst (ConstFloat f) -> 
      fprintf fmt "%f" f
  | Tbound b ->
      fprintf fmt "#%d" (Ident.bound_id b)
  | Tvar id -> 
      fprintf fmt "%s" (Ident.string id)
  | Tapp (id, tl) -> 
      fprintf fmt "%s(" (Ident.string id);
      print_list fmt comma print_term tl; fprintf fmt ")"

let rec print_predicate fmt = function
  | Pterm t -> print_term fmt t
  | Pimplies (a, b) -> 
      fprintf fmt "(@["; print_predicate fmt a; fprintf fmt " ->@ ";
      print_predicate fmt b; fprintf fmt "@])"
  | Pif (a, b, c) -> 
      fprintf fmt "(@[if "; print_predicate fmt a; fprintf fmt " then@ ";
      print_predicate fmt b; fprintf fmt " else@ ";
      print_predicate fmt c; fprintf fmt "@])"
  | Pand (a, b) ->
      fprintf fmt "(@["; print_predicate fmt a; fprintf fmt " and@ ";
      print_predicate fmt b; fprintf fmt "@])"
  | Por (a, b) ->
      fprintf fmt "(@["; print_predicate fmt a; fprintf fmt " or@ ";
      print_predicate fmt b; fprintf fmt "@])"
  | Pnot a ->
      fprintf fmt "(not "; print_predicate fmt a; fprintf fmt ")"
  | Forall (_,b,_,p) ->
      fprintf fmt "(forall #%d: " (Ident.bound_id b);
      print_predicate fmt p; fprintf fmt ")"

