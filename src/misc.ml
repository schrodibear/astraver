
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: misc.ml,v 1.3 2001-08-19 02:44:48 filliatr Exp $ *)

open Ident
open Logic

(* debug *)

let debug = ref false

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

(* TODO: these functions should be moved in the code of Coq *)

let reraise_with_loc loc f x =
  try f x with e -> Stdpp.raise_with_loc loc e


(* functions on names *)

let at_id id d = Ident.create ((Ident.string id) ^ "@" ^ d)

let is_at id =
  try
    let _ = String.index (Ident.string id) '@' in true
  with Not_found ->
    false

let un_at id =
  let s = Ident.string id in
    try
      let n = String.index s '@' in
    	Ident.create (String.sub s 0 n),
	String.sub s (succ n) (pred (String.length s - n))
    with Not_found ->
      invalid_arg "un_at"

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

let adr_id id = Ident.create ("adr_" ^ (Ident.string id))

(* hypotheses names *)

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
  | Tconst _, _ -> assert false

let rec collect_term s = function
  | Tvar id -> Idset.add id s
  | Tapp (_, l) -> List.fold_left collect_term s l
  | Tconst _ -> s

and collect_pred s = function
  | Pterm t -> collect_term s t
  | Pimplies (a, b) | Pand (a, b) | Por (a, b) -> 
      collect_pred (collect_pred s a) b
  | Pif (a, b, c) -> collect_pred (collect_pred (collect_pred s a) b) c
  | Pnot a -> collect_pred s a

let term_vars = collect_term Idset.empty
let predicate_vars = collect_pred Idset.empty

let rec tsubst_in_term alist = function
  | Tvar x as t -> (try List.assoc x alist with Not_found -> t)
  | Tapp (x,l) -> Tapp (x, List.map (tsubst_in_term alist) l)
  | Tconst _ as t -> t

let rec tsubst_in_predicate alist = function
  | Pterm t -> Pterm (tsubst_in_term alist t)
  | Pimplies (a, b) -> Pimplies (tsubst_in_predicate alist a,
				 tsubst_in_predicate alist b)
  | Pif (a,b,c) -> Pif (tsubst_in_predicate alist a,
			tsubst_in_predicate alist b,
			tsubst_in_predicate alist c)
  | Pand (a,b) -> Pand (tsubst_in_predicate alist a,
			tsubst_in_predicate alist b)
  | Por (a,b) -> Por (tsubst_in_predicate alist a,
		      tsubst_in_predicate alist b)
  | Pnot a -> Pnot (tsubst_in_predicate alist a)

let subst_in_term alist = 
  tsubst_in_term (List.map (fun (id,id') -> (id, Tvar id')) alist)
let subst_in_predicate alist = 
  tsubst_in_predicate (List.map (fun (id,id') -> (id, Tvar id')) alist)

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

(*s Pretty-print *)

open Format

let rec print_list fmt sep print = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list fmt sep print r

let comma fmt () = fprintf fmt ",@ "
let nothing fmt () = ()

let hov n fmt f x = pp_open_hovbox fmt n; f fmt x; pp_close_box fmt ()

let rec print_term fmt = function
  | Tconst _ -> fprintf fmt "<const>"
  | Tvar id -> fprintf fmt "%s" (Ident.string id)
  | Tapp (id, tl) -> 
      fprintf fmt "%s(" (Ident.string id);
      print_list fmt comma print_term tl; fprintf fmt ")"

let rec print_predicate fmt = function
  | Pterm t -> print_term fmt t
  | Pimplies (a, b) -> 
      fprintf fmt "("; print_predicate fmt a; fprintf fmt " ->@ ";
      print_predicate fmt b; fprintf fmt ")"
  | Pif (a, b, c) -> 
      fprintf fmt "(if"; print_predicate fmt a; fprintf fmt " then@ ";
      print_predicate fmt b; fprintf fmt " else@ ";
      print_predicate fmt c; fprintf fmt ")"
  | Pand (a, b) ->
      fprintf fmt "("; print_predicate fmt a; fprintf fmt " and@ ";
      print_predicate fmt b; fprintf fmt ")"
  | Por (a, b) ->
      fprintf fmt "("; print_predicate fmt a; fprintf fmt " or@ ";
      print_predicate fmt b; fprintf fmt ")"
  | Pnot a ->
      fprintf fmt "(not "; print_predicate fmt a; fprintf fmt ")"

(*i
(* functions on CIC terms *)

let isevar = Evarutil.new_evar_in_sign (Global.env ())

(* Substitutions of variables by others. *)
let subst_in_constr alist =
  let alist' = List.map (fun (id,id') -> (id, mkVar id')) alist in
  replace_vars alist'

let subst_in_ast alist ast =
  let alist' = 
    List.map (fun (id,id') -> (string_of_id id,string_of_id id')) alist in
  let rec subst = function
      Nvar(l,s) -> Nvar(l,try List.assoc s alist' with Not_found -> s)
    | Node(l,s,args) -> Node(l,s,List.map subst args)
    | Slam(l,so,a) -> Slam(l,so,subst a) (* TODO:enlever so de alist' ? *)
    | x -> x
  in
    subst ast

let subst_ast_in_ast alist ast =
  let alist' = 
    List.map (fun (id,a) -> (string_of_id id,a)) alist in
  let rec subst = function
      Nvar(l,s) as x -> (try List.assoc s alist' with Not_found -> x)
    | Node(l,s,args) -> Node(l,s,List.map subst args)
    | Slam(l,so,a) -> Slam(l,so,subst a) (* TODO:enlever so de alist' ? *)
    | x -> x
  in
    subst ast

(* subst. of variables by constr *)
let real_subst_in_constr = replace_vars

(* Coq constants *)

let coq_constant d s = make_path ("Coq" :: d) (id_of_string s) CCI

let bool_sp = coq_constant ["Init"; "Datatypes"] "bool"
let coq_true = mkMutConstruct (((bool_sp,0),1), [||])
let coq_false = mkMutConstruct (((bool_sp,0),2), [||])

let constant s =
  let id = id_of_string s in
  Declare.global_reference CCI id

let connective_and = id_of_string "prog_bool_and"
let connective_or  = id_of_string "prog_bool_or"
let connective_not = id_of_string "prog_bool_not"

let is_connective id =
  id = connective_and or id = connective_or or id = connective_not

(* [conj i s] constructs the conjunction of two constr *)

let conj i s = Term.applist (constant "and", [i; s])

(* [n_mkNamedProd v [xn,tn;...;x1,t1]] constructs the type 
   [(x1:t1)...(xn:tn)v] *)

let rec n_mkNamedProd v = function
  | [] -> v
  | (id,ty) :: rem -> n_mkNamedProd (Term.mkNamedProd id ty v) rem

(* [n_lambda v [xn,tn;...;x1,t1]] constructs the type [x1:t1]...[xn:tn]v *)

let rec n_lambda v = function
  | [] -> v
  | (id,ty) :: rem -> n_lambda (Term.mkNamedLambda id ty v) rem

(* [abstract env idl c] constructs [x1]...[xn]c where idl = [x1;...;xn] *)

let abstract ids c = n_lambda c (List.rev ids)


i*)
