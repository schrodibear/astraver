(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: misc.ml,v 1.13 2002-03-05 14:51:26 filliatr Exp $ i*)

open Ident
open Logic
open Types 
open Ast

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

let rec list_combine3 a b c = match a, b, c with
  | [], [], [] -> []
  | xa::ra, xb::rb, xc::rc -> (xa, xb, xc) :: list_combine3 ra rb rc
  | _ -> invalid_arg "list_combine3"

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

(*s Various utility functions. *)

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function PureType _ -> true | _ -> false

let named_app f x = { a_name = x.a_name; a_value = (f x.a_value) }

let pre_app f x = 
  { p_assert = x.p_assert; p_name = x.p_name; p_value = f x.p_value }

let post_app = named_app

let anonymous x = { a_name = Anonymous; a_value = x }

let anonymous_pre b x = { p_assert = b; p_name = Anonymous; p_value = x }

let force_name f x =
  option_app (fun q -> { a_name = Name (f q.a_name); a_value = q.a_value }) x

let force_post_name x = force_name post_name x

let force_bool_name x = 
  force_name (function Name id -> id | Anonymous -> bool_name()) x

let out_post = function
    Some { a_value = x } -> x
  | None -> invalid_arg "out_post"

let pre_of_assert b x =
  { p_assert = b; p_name = x.a_name; p_value = x.a_value }

let assert_of_pre x =
  { a_name = x.p_name; a_value = x.p_value }

(*s Functions on terms and predicates. *)

let applist f l = match (f,l) with
  | f, [] -> f
  | Tvar id, l -> Tapp (id, l)
  | Tapp (id, l), l' -> Tapp (id, l @ l')
  | (Tbound _ | Tconst _), _ -> assert false

let papplist f l = match (f,l) with
  | f, [] -> f
  | Pvar id, l -> Papp (id, l)
  | Papp (id, l), l' -> Papp (id, l @ l')
  | _ -> assert false

let rec collect_term s = function
  | Tvar id -> Idset.add id s
  | Tapp (_, l) -> List.fold_left collect_term s l
  | Tconst _ | Tbound _ -> s

and collect_pred s = function
  | Pvar _ | Ptrue | Pfalse -> s
  | Papp (_, l) -> List.fold_left collect_term s l
  | Pimplies (a, b) | Pand (a, b) | Por (a, b) -> 
      collect_pred (collect_pred s a) b
  | Pif (a, b, c) -> collect_pred (collect_pred (collect_term s a) b) c
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
  | Pif (a, b, c) -> Pif (a, f b, f c)
  | Pand (a, b) -> Pand (f a, f b)
  | Por (a, b) -> Por (f a, f b)
  | Pnot a -> Pnot (f a)
  | Forall (id, b, v, p) -> Forall (id, b, v, f p)
  | Ptrue | Pfalse | Pvar _ | Papp _ as p -> p

let rec tsubst_in_predicate alist = function
  | Papp (id, l) -> Papp (id, List.map (tsubst_in_term alist) l)
  | Pif (a, b ,c) -> Pif (tsubst_in_term alist a, 
			  tsubst_in_predicate alist b, 
			  tsubst_in_predicate alist c)
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
  | Papp (id, l) -> Papp (id, List.map (bsubst_in_term alist) l)
  | p -> map_predicate (bsubst_in_predicate alist) p

let equals_true = function
  | Tapp (id, _) as t when is_relation id -> t
  | t -> Tapp (t_eq, [t; Tconst (ConstBool true)])

let negate id =
  if id == t_lt then t_ge
  else if id == t_le then t_gt 
  else if id == t_gt then t_le
  else if id == t_ge then t_lt
  else if id == t_eq then t_neq
  else if id == t_neq then t_eq
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
  | Pvar _ | Ptrue | Pfalse -> false
  | Papp (_, l) -> List.exists (occur_term id) l
  | Pif (a, b, c) -> 
      occur_term id a || occur_predicate id b || occur_predicate id c
  | Pimplies (a, b) -> occur_predicate id a || occur_predicate id b
  | Pand (a, b) -> occur_predicate id a || occur_predicate id b
  | Por (a, b) -> occur_predicate id a || occur_predicate id b
  | Pnot a -> occur_predicate id a
  | Forall (_,_,_,a) -> occur_predicate id a
  
(*s Smart constructors. *)

let ttrue = Tconst (ConstBool true)
let tfalse = Tconst (ConstBool false)
let tresult = Tvar Ident.result

let relation op t1 t2 = Papp (op, [t1; t2])
let not_relation op = relation (negate op)
let lt = relation t_lt
let le = relation t_le
let gt = relation t_gt
let ge = relation t_ge
let eq = relation t_eq
let neq = relation t_neq

let pif a b c =
  if a = ttrue then b else if a = tfalse then c else Pif (a, b ,c)

let pand a b = 
  if a = Ptrue then b else if b = Ptrue then a else
  if a = Pfalse || b = Pfalse then Pfalse else
  Pand (a, b)

let por a b =
  if a = Ptrue || b = Ptrue then Ptrue else
  if a = Pfalse then b else if b = Pfalse then a else
  Por (a, b)

let pnot a =
  if a = Ptrue then Pfalse else if a = Pfalse then Ptrue else Pnot a

(*s functions over AST *)

let arg_loc = function 
  | Term t -> t.info.loc 
  | Refarg (l,_) -> l 
  | Type _ -> assert false (* TODO *)

(*s Pretty-print *)

open Format

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let comma fmt () = fprintf fmt ",@ "
let arrow fmt () = fprintf fmt "@ -> "
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
      fprintf fmt "%s(%a)" (Ident.string id) (print_list comma print_term) tl

let relation_string id =
  if id == t_lt then "<" 
  else if id == t_le then "<="
  else if id == t_gt then ">"
  else if id == t_ge then ">="
  else if id == t_eq then "="
  else if id == t_neq then "<>"
  else assert false

let rec print_predicate fmt = function
  | Pvar id -> 
      Ident.print fmt id
  | Papp (id, [t1; t2]) when is_relation id ->
      fprintf fmt "%a %s %a" print_term t1 (relation_string id) print_term t2
  | Papp (id, l) ->
      fprintf fmt "%s(%a)" (Ident.string id) (print_list comma print_term) l
  | Ptrue ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pimplies (a, b) -> 
      fprintf fmt "(@["; print_predicate fmt a; fprintf fmt " ->@ ";
      print_predicate fmt b; fprintf fmt "@])"
  | Pif (a, b, c) -> 
      fprintf fmt "(@[if "; print_term fmt a; fprintf fmt " then@ ";
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

