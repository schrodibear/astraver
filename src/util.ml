(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: util.ml,v 1.41 2002-07-09 11:45:02 filliatr Exp $ i*)

open Logic
open Ident
open Misc
open Types
open Ast
open Env
open Rename

(*s References mentioned by a predicate *)

let is_reference env id =
  (is_in_env env id) && (is_mutable (type_in_env env id))

let predicate_now_refs env c =
  Idset.filter (is_reference env) (predicate_vars c)

let term_now_refs env c =
  Idset.filter (is_reference env) (term_vars c)


let labelled_reference env id =
  if is_reference env id then
    id
  else if is_at id then
    let uid,_ = Ident.un_at id in 
    if is_reference env uid then uid else failwith "caught"
  else
    failwith "caught"

let set_map_succeed f s = 
  Idset.fold 
    (fun x e -> try Idset.add (f x) e with Failure _ -> e) 
    s Idset.empty

let predicate_refs env c =
  set_map_succeed (labelled_reference env) (predicate_vars c)

let term_refs env c =
  set_map_succeed (labelled_reference env) (term_vars c)

(*s Labels management *)

let gen_change_label f c =
  let ids = Idset.elements (predicate_vars c) in
  let s = 
    List.fold_left 
      (fun s id -> 
	 if is_at id then 
	   try Idmap.add id (f (un_at id)) s with Failure _ -> s
	 else s)
      Idmap.empty ids
  in
  subst_in_predicate s c

let erase_label l c =
  gen_change_label 
    (function (uid,l') when l = l' -> uid | _ -> failwith "caught") c

let change_label l1 l2 c =
  gen_change_label 
    (function (uid,l) when l = l1 -> at_id uid l2 | _ -> failwith "caught") c

let put_label_term env l t =
  let ids = term_refs env t in
  let s = 
    Idset.fold (fun id s -> Idmap.add id (at_id id l) s) ids Idmap.empty 
  in
  subst_in_term s t

(*s shortcuts for typing information *)

let effect p = p.info.kappa.c_effect
let pre p = p.info.kappa.c_pre
let post p = p.info.kappa.c_post
let result_type p = p.info.kappa.c_result_type
let result_name p = p.kappa.c_result_name

let erase_exns ti = 
  let k = ti.kappa in
  { ti with kappa = { k with c_effect = Effect.erase_exns k.c_effect } }

(*s [apply_pre] and [apply_post] instantiate pre- and post- conditions
    according to a given renaming of variables (and a date that means
    `before' in the case of the post-condition). *)

let make_subst before ren env ids =
  Idset.fold
    (fun id s ->
       if is_reference env id then
	 Idmap.add id (current_var ren id) s
       else if is_at id then
	 let uid,d = un_at id in
	 if is_reference env uid then begin
	   let d' = match d, before with
	     | "", None -> assert false
	     | "", Some l -> l
	     | _ -> d
	   in
	   Idmap.add id (var_at_date ren d' uid) s
	 end else
	   s
       else
	 s) 
    ids Idmap.empty

let apply_term ren env t =
  let ids = term_vars t in
  let s = make_subst None ren env ids in
  subst_in_term s t

let apply_pre ren env c =
  let ids = predicate_vars c.p_value in
  let s = make_subst None ren env ids in
  { p_assert = c.p_assert; p_name = c.p_name; 
    p_value = subst_in_predicate s c.p_value }

let apply_assert ren env c =
  let ids = predicate_vars c.a_value in
  let s = make_subst None ren env ids in
  { a_name = c.a_name; a_value = subst_in_predicate s c.a_value }
 
let apply_post before ren env c =
  let ids = predicate_vars c.a_value in
  let s = make_subst (Some before) ren env ids in
  { a_name = c.a_name; a_value = subst_in_predicate s c.a_value }
  
(*s [traverse_binder ren env bl] updates renaming [ren] and environment [env]
    as we cross the binders [bl]. *)

let rec traverse_binders env = function
  | [] -> 
      env
  | (id, BindType v) :: rem ->
      traverse_binders (Env.add id v env) rem
  | (id, BindSet) :: rem ->
      traverse_binders (Env.add_set id env) rem
  | (_, Untyped) :: _ ->
      invalid_arg "traverse_binders"
	  
let initial_renaming env =
  let ids = Env.fold_all (fun (id,_) l -> id::l) env [] in
  update empty_ren "init" ids


(*s Occurrences *)

let rec occur_term id = function
  | Tvar id' -> id = id'
  | Tapp (_, l) -> List.exists (occur_term id) l
  | Tconst _ -> false

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

let occur_assertion id a = occur_predicate id a.a_value

let occur_precondition id p = occur_predicate id p.p_value
  
let occur_post id = function None -> false | Some q -> occur_assertion id q

let rec occur_type_v id = function
  | Ref v -> occur_type_v id v
  | Array (t, v) -> occur_term id t || occur_type_v id v
  | Arrow (bl, c) -> occur_arrow id bl c
  | PureType _ -> false

and occur_type_c id c =
  occur_type_v id c.c_result_type ||
  List.exists (occur_precondition id) c.c_pre ||
  Effect.occur id c.c_effect ||
  occur_post id c.c_post 

and occur_arrow id bl c = match bl with
  | [] -> 
      occur_type_c id c
  | (id', BindType v) :: bl' -> 
      occur_type_v id v || (id <> id' && occur_arrow id bl' c)
  | (_, (BindSet | Untyped)) :: bl' -> 
      occur_arrow id bl' c

let forall x v p =
  let n = Ident.bound x in
  let p = subst_in_predicate (subst_onev x n) p in
  Forall (x, n, mlize_type v, p)

let foralls =
  List.fold_right
    (fun (x,v) p -> if occur_predicate x p then forall x v p else p)
    
(* misc. functions *)

let deref_type = function
  | Ref v -> v
  | _ -> invalid_arg "deref_type"

let dearray_type = function
  | Array (size,v) -> size,v
  | _ -> invalid_arg "dearray_type"

let decomp_kappa c = 
  ((c.c_result_name, c.c_result_type), c.c_effect, c.c_pre, c.c_post)

let id_from_name = function Name id -> id | Anonymous -> (Ident.create "X")

(* [decomp_boolean c] returns the specs R and S of a boolean expression *)

let equality t1 t2 = Papp (t_eq, [t1; t2])

let decomp_boolean = function
  | Some { a_value = c } -> 
      (* q -> if result then q(true) else q(false) *)
      let ctrue = tsubst_in_predicate (subst_one Ident.result ttrue) c in
      let cfalse = tsubst_in_predicate (subst_one Ident.result tfalse) c in
      simplify ctrue, simplify cfalse
  | None -> 
      equality (Tvar Ident.result) ttrue,
      equality (Tvar Ident.result) tfalse

(*s [make_access env id c] Access in array id.
    Constructs [t:(array s T)](access_g s T t c ?::(lt c s)). *)

let array_info env id =
  let ty = type_in_env env id in
  let size,v = dearray_type ty in
  (*i let ty_elem = trad_ml_type_v ren env v in
  let ty_array = trad_imp_type ren env ty in i*)
  size,v

let make_raw_access env (id,id') c =
  let size,_ = array_info env id in
  Tapp (Ident.access, [Tvar id'; c])

let make_pre_access env id c =
  let size,_ = array_info env id in
  Pand (le_int (Tconst (ConstInt 0)) c, lt_int c size)
      
let make_raw_store env (id,id') c1 c2 =
  let size,_ = array_info env id in
  Tapp (Ident.store, [Tvar id'; c1; c2])

(*s Pretty printers (for debugging purposes) *)

open Format

let print_pre fmt l = 
  if l <> [] then begin
    fprintf fmt "@[ ";
    print_list 
      pp_print_space (fun fmt p -> print_predicate fmt p.p_value) fmt l;
    fprintf fmt " @]"
  end

let print_post fmt = function
  | None -> ()
  | Some c -> fprintf fmt "@[ %a @]" print_predicate c.a_value

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTfloat -> fprintf fmt "float"
  | PTarray (s,t) -> fprintf fmt "array(%a,%a)" print_term s print_pure_type t
  | PTexternal id -> fprintf fmt "%s" (Ident.string id)

and print_type_v fmt = function
  | Arrow (b,c) ->
      fprintf fmt "@[<hov 2>%a ->@ %a@]" 
	(print_list arrow pp_binder) b print_type_c c
  | v -> 
      print_type_v2 fmt v

and pp_binder fmt = function
  | id, BindType v when id == Ident.anonymous -> 
      print_type_v2 fmt v
  | id, BindType v ->
      fprintf fmt "@[%a:%a@]" Ident.print id print_type_v v; 
  | id, BindSet -> 
      fprintf fmt "%a:Set" Ident.print id
  | id, Untyped -> 
      fprintf fmt "<untyped>"

and print_type_v2 fmt = function
  | Ref v -> 
      fprintf fmt "@[%a@ ref@]" print_type_v v
  | Array (cc,v) -> 
      fprintf fmt "@[array@ %a@ of %a@]" print_term cc print_type_v v
  | PureType pt -> 
      print_pure_type fmt pt
  | Arrow _ as v ->
      fprintf fmt "(%a)" print_type_v v

and print_type_c fmt c =
  let id = c.c_result_name in
  let v = c.c_result_type in
  let p = c.c_pre in
  let q = c.c_post in
  let e = c.c_effect in
  if e = Effect.bottom && p = [] && q = None then
    print_type_v fmt v
  else
    fprintf fmt "@[{%a}@ returns %a: %a@ %a@,{%a}@]" 
      print_pre p
      Ident.print id 
      print_type_v v 
      Effect.print e
      print_post q

(*s Pretty-print of typed programs *)

let rec print_prog fmt p = 
  let k = p.info.kappa in
  if k.c_pre = [] && k.c_post = None then
    fprintf fmt "@[%s:@,%a@]" p.info.label print_desc p.desc
  else
    fprintf fmt "@[%s:@,@[{%a}@ %a@ @]{%a}@]" 
      p.info.label print_pre k.c_pre print_desc p.desc print_post k.c_post

and print_desc fmt = function
  | Var id -> 
      Ident.print fmt id
  | Acc id -> 
      fprintf fmt "!%a" Ident.print id
  | Aff (id, p) -> 
      fprintf fmt "@[%a :=@ %a@]" Ident.print id print_prog p
  | TabAcc (_, id, p) -> 
      fprintf fmt "%a[%a]" Ident.print id print_prog p
  | TabAff (_, id, p1, p2) -> 
      fprintf fmt "%a[%a] :=@ %a" Ident.print id print_prog p1 print_prog p2
  | Seq bl -> 
      fprintf fmt "begin@\n  @[%a@]@\nend" print_block bl
  | While (p, i, var, e) ->
      fprintf fmt 
	"while %a do@\n  { invariant %a variant _ }@\n  @[%a@]@\ndone" 
	print_prog p print_post i print_prog e
  | If (p1, p2, p3) ->
      fprintf fmt "if %a then@ %a else@ %a" 
	print_prog p1 print_prog p2 print_prog p3
  | Lam (bl, p) -> 
      fprintf fmt "<fun>"
  | App (p, a, k) -> 
      fprintf fmt "(@[%a %a ::@ %a@])" print_prog p print_arg a print_type_c k
  | LetRef (id, p1, p2) ->
      fprintf fmt "let %a = ref %a in@ %a" 
	Ident.print id print_prog p1 print_prog p2
  | LetIn (id, p1, p2) ->
      fprintf fmt "let %a = %a in@ %a" 
	Ident.print id print_prog p1 print_prog p2
  | Rec (id, bl, v, var, p) ->
      fprintf fmt "rec %a : <bl> %a { variant _ } =@\n%a" 
	Ident.print id print_type_v v print_prog p
  | Raise (id, None, t) ->
      fprintf fmt "raise %a" Ident.print id; print_cast fmt t
  | Raise (id, Some p, t) ->
      fprintf fmt "raise (%a %a)" Ident.print id print_prog p; print_cast fmt t
  | Expression t -> 
      print_term fmt t
  | Coerce p ->
      print_prog fmt p

and print_cast fmt = function
  | None -> ()
  | Some v -> fprintf fmt ": %a" print_type_v v

and print_block fmt = 
  print_list (fun fmt () -> fprintf fmt ";@\n") print_block_st fmt

and print_block_st fmt = function
  | Statement p -> print_prog fmt p
  | Label l -> fprintf fmt "label %s" l
  | Assert a -> fprintf fmt "assert {%a}" print_assertion a

and print_arg fmt = function
  | Term p -> print_prog fmt p
  | Refarg id -> Ident.print fmt id
  | Type v -> print_type_v fmt v

(*s Pretty-print of cc-terms (intermediate terms) *)

let print_pred_binders = ref true
let print_var_binders = ref false

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray (s, t) -> 
      fprintf fmt "(array %a %a)" print_term s print_cc_type t
  | TTlambda (b, t) ->
      fprintf fmt "[%a]%a" print_binder b print_cc_type t
  | TTarrow (b, t) -> 
      fprintf fmt "(%a)%a" print_binder b print_cc_type t
  | TTtuple (bl, None) -> 
      fprintf fmt "{%a}" print_tuple bl
  | TTtuple (bl, Some q) -> 
      fprintf fmt "{%a | %a}" print_tuple bl print_cc_type q
  | TTpred p ->
      print_predicate fmt p
  | TTapp (id, t) ->
      fprintf fmt "(%a %a)" Ident.print id print_cc_type t

and print_tuple fmt =
  print_list comma 
    (fun fmt (id,t) -> fprintf fmt "%a:%a" Ident.print id print_cc_type t) fmt

and print_binder fmt (id,b) = 
  Ident.print fmt id;
  match b with
    | CC_pred_binder p -> 
	if !print_pred_binders then fprintf fmt ": %a" print_predicate p
    | CC_var_binder t -> 
	if !print_var_binders then fprintf fmt ": %a" print_cc_type t
    | CC_untyped_binder -> 
	()

let rec print_cc_term fmt = function
  | CC_var id -> 
      fprintf fmt "%s" (Ident.string id)
  | CC_letin (_,bl,c,c1) ->
      fprintf fmt "@[@[<hov 2>let %a =@ %a in@]@\n%a@]"
      (print_list comma print_binder) bl
      print_cc_term c print_cc_term c1
  | CC_lam (b,c) ->
      fprintf fmt "@[<hov 2>[%a]@,%a@]" print_binder b print_cc_term c
  | CC_app (f,a) ->
      fprintf fmt "@[<hov 2>(%a@ %a)@]" print_cc_term f print_cc_term a
  | CC_tuple (cl,_) ->
      fprintf fmt "@[<hov 2>(%a)@]" (print_list comma print_cc_term) cl
  | CC_if (b,e1,e2) ->
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (print_cc_term fmt) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (print_cc_term fmt) e2;
      fprintf fmt "@]"
  | CC_term c ->
      fprintf fmt "@["; print_term fmt c; fprintf fmt "@]"
  | CC_hole c ->
      fprintf fmt "@[(?:@ "; print_predicate fmt c; fprintf fmt ")@]"
  | CC_type t ->
      print_cc_type fmt t

and print_binders fmt bl =
  print_list nothing (fun fmt b -> fprintf fmt "[%a]" print_binder b) fmt bl


let print_subst fmt =
  Idmap.iter
    (fun id t -> fprintf fmt "%a -> %a@\n" Ident.print id print_term t)

let print_cc_subst fmt =
  Idmap.iter
    (fun id t -> fprintf fmt "%a -> %a@\n" Ident.print id print_cc_term t)


let print_env fmt e =
  let print_type_info fmt = function
    | Set -> fprintf fmt "Set"
    | TypeV v -> print_type_v fmt v
  in
  fold_all (fun (id, v) () -> fprintf fmt "%a:%a, " Ident.dbprint id 
		print_type_info v) e ()

