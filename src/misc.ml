(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: misc.ml,v 1.35 2002-05-07 15:53:23 filliatr Exp $ i*)

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

let option_iter f = function None -> () | Some x -> f x

let list_of_some = function None -> [] | Some x -> [x]

let if_labelled f id = if is_at id then f (un_at id)

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

let rec list_first f = function
  | [] -> raise Exit
  | x :: l -> try f x with Exit -> list_first f l

(*s Functions on names *)

type avoid = Ident.set

let renaming_of_ids avoid ids =
  let rec rename avoid = function
    | [] -> 
	[], avoid
    | x :: rem ->
	let al,avoid = rename avoid rem in
	let x' = Ident.next_away x avoid in
	(x,x')::al, Idset.add x' avoid
  in
  rename avoid ids

(*s hypotheses names *)

let next s r = function
  | Anonymous -> incr r; Ident.create (s ^ string_of_int !r)
  | Name id -> id

let reset_names_tables = ref []
let reset_names () = List.iter (fun f -> f ()) !reset_names_tables

let gen_sym_name s =
  let r = ref 0 in 
  reset_names_tables := (fun () -> r := 0) :: !reset_names_tables;
  next s r

let gen_sym s = let g = gen_sym_name s in fun () -> g Anonymous

let pre_name = gen_sym_name "Pre"
let post_name = gen_sym_name "Post"
let inv_name = gen_sym_name "Inv"
let test_name = gen_sym_name "Test"
let bool_name = gen_sym "Bool"
let variant_name = gen_sym "Variant"
let phi_name = gen_sym "rphi"
let for_name = gen_sym "for"
let label_name = let f = gen_sym "_label_" in fun () -> Ident.string (f ())
let fresh_var = gen_sym "aux_"
let wf_name = gen_sym "wf"

let id_of_name = function Name id -> id | Anonymous -> default

let warning s = Format.eprintf "warning: %s\n" s

(*s Various utility functions. *)

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function PureType _ -> true | _ -> false

let named_app f x = { a_name = x.a_name; a_value = (f x.a_value) }

let pre_app f x = 
  { p_assert = x.p_assert; p_name = x.p_name; p_value = f x.p_value }

let post_app = named_app

let optpost_app f = option_app (post_app f)

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
  | Tconst _, _ -> assert false

let papplist f l = match (f,l) with
  | f, [] -> f
  | Pvar id, l -> Papp (id, l)
  | Papp (id, l), l' -> Papp (id, l @ l')
  | _ -> assert false

let rec predicate_of_term = function
  | Tvar x -> Pvar x
  | Tapp (id, l) -> Papp (id, l)
  | _ -> assert false

let rec collect_term s = function
  | Tvar id -> Idset.add id s
  | Tapp (_, l) -> List.fold_left collect_term s l
  | Tconst _ -> s

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

let rec tsubst_in_term s = function
  | Tvar x as t -> 
      (try Idmap.find x s with Not_found -> t)
  | Tapp (x,l) -> 
      Tapp (x, List.map (tsubst_in_term s) l)
(*i***EXP
      let l' = List.map (tsubst_in_term s) l in
      (try applist (Idmap.find x s) l' with Not_found -> Tapp (x,l'))
***i*)
  | Tconst _ as t -> 
      t

let rec map_predicate f = function
  | Pimplies (a, b) -> Pimplies (f a, f b)
  | Pif (a, b, c) -> Pif (a, f b, f c)
  | Pand (a, b) -> Pand (f a, f b)
  | Por (a, b) -> Por (f a, f b)
  | Pnot a -> Pnot (f a)
  | Forall (id, b, v, p) -> Forall (id, b, v, f p)
  | Ptrue | Pfalse | Pvar _ | Papp _ as p -> p

let rec tsubst_in_predicate s = function
  | Papp (id, l) -> Papp (id, List.map (tsubst_in_term s) l)
  | Pif (a, b ,c) -> Pif (tsubst_in_term s a, 
			  tsubst_in_predicate s b, 
			  tsubst_in_predicate s c)
  | p -> map_predicate (tsubst_in_predicate s) p

let subst_in_term s = 
  tsubst_in_term (Idmap.map (fun id -> Tvar id) s)

let subst_in_predicate s = 
  tsubst_in_predicate (Idmap.map (fun id -> Tvar id) s)

let subst_one x t = Idmap.add x t Idmap.empty

let subst_onev = subst_one

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

(*s Substitutions *)

let rec type_c_subst s c =
  let {c_result_name=id; c_result_type=t; c_effect=e; c_pre=p; c_post=q} = c in
  let s' = Idmap.fold (fun x x' -> Idmap.add (at_id x "") (at_id x' "")) s s in
  { c_result_name = id;
    c_result_type = type_v_subst s t;
    c_effect = Effect.subst s e;
    c_pre = List.map (pre_app (subst_in_predicate s)) p;
    c_post = option_app (post_app (subst_in_predicate s')) q }

and type_v_subst s = function
  | Ref v -> Ref (type_v_subst s v)
  | Array (n,v) -> Array (n,type_v_subst s v)
  | Arrow (bl,c) -> Arrow (List.map (binder_subst s) bl, type_c_subst s c)
  | (PureType _) as v -> v

and binder_subst s = function
  | (n, BindType v) -> (n, BindType (type_v_subst s v))
  | b -> b

(*s substitution of term for variables *)

let rec type_c_rsubst s c =
  { c_result_name = c.c_result_name;
    c_result_type = type_v_rsubst s c.c_result_type;
    c_effect = c.c_effect;
    c_pre = List.map (pre_app (tsubst_in_predicate s)) c.c_pre;
    c_post = option_app (post_app (tsubst_in_predicate s)) c.c_post }

and type_v_rsubst s = function
  | Ref v -> Ref (type_v_rsubst s v)
  | Array (n,v) -> Array (tsubst_in_term s n, type_v_rsubst s v)
  | Arrow (bl,c) -> Arrow(List.map (binder_rsubst s) bl, type_c_rsubst s c)
  | PureType _ as v -> v

and binder_rsubst s = function
  | (n, BindType v) -> (n, BindType (type_v_rsubst s v))
  | b -> b

let type_c_of_v v =
  { c_result_name = Ident.result;
    c_result_type = v;
    c_effect = Effect.bottom; c_pre = []; c_post = None }

(* make_arrow bl c = (x1:V1)...(xn:Vn)c *)

let make_arrow bl c = match bl with
  | [] -> 
      invalid_arg "make_arrow: no binder"
  | _ -> 
      let rename (id,v) (bl,s) = 
	let id' = Ident.bound id in 
	(id',v) :: bl, 
	Idmap.add id id' (Idmap.add (at_id id "") (at_id id' "") s)
      in
      let bl',s = List.fold_right rename bl ([], Idmap.empty) in
      Arrow (bl', type_c_subst s c)

(*s Smart constructors. *)

let ttrue = Tconst (ConstBool true)
let tfalse = Tconst (ConstBool false)
let tresult = Tvar Ident.result
let tvoid = Tconst ConstUnit

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

(*s [simplify] only performs simplications which are Coq reductions.
     Currently: only [if true] and [if false] *)

let rec simplify = function
  | Pif (Tconst (ConstBool true), a, _) -> simplify a
  | Pif (Tconst (ConstBool false), _, b) -> simplify b
  | p -> map_predicate simplify p

(*s functions over CC terms *)

let rec cc_applist f l = match (f, l) with
  | f, [] -> f
  | f, x :: l -> cc_applist (CC_app (f, x)) l

let cc_lam bl = List.fold_right (fun b c -> CC_lam (b, c)) bl

let tt_arrow = List.fold_right (fun b t -> TTarrow (b, t))

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
let space fmt () = fprintf fmt "@ "
let arrow fmt () = fprintf fmt "@ -> "
let nothing fmt () = ()
let string fmt s = fprintf fmt "%s" s

let hov n fmt f x = pp_open_hovbox fmt n; f x; pp_close_box fmt ()

let rec print_term fmt = function
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "void" 
  | Tconst (ConstFloat f) -> 
      fprintf fmt "%f" f
  | Tvar id -> 
      Ident.print fmt id
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
      fprintf fmt "(@[%a ->@ %a@])" print_predicate a print_predicate b
  | Pif (a, b, c) -> 
      fprintf fmt "(@[if %a then@ %a else@ %a@])" 
	print_term a print_predicate b print_predicate c
  | Pand (a, b) ->
      fprintf fmt "(@[%a and@ %a@])" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "(@[%a or@ %a@])" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "(not %a)" print_predicate a
  | Forall (_,b,_,p) ->
      fprintf fmt "@[<hov 2>(forall %a:@ %a)@]" 
	Ident.print b print_predicate p

let print_assertion fmt a = print_predicate fmt a.a_value

let print_wp fmt = function
  | None -> fprintf fmt "<no weakest precondition>"
  | Some {a_value=p} -> print_predicate fmt p
