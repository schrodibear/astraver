(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: util.ml,v 1.22 2002-03-15 15:44:08 filliatr Exp $ i*)

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
  let al = 
    map_succeed
      (function id -> 
	 if is_at id then (id, f (un_at id)) else failwith "caught")
      ids
  in
  subst_in_predicate al c

let erase_label l c =
  gen_change_label 
    (function (uid,l') when l = l' -> uid | _ -> failwith "caught") c

let change_label l1 l2 c =
  gen_change_label 
    (function (uid,l) when l = l1 -> at_id uid l2 | _ -> failwith "caught") c

let put_label_term env l t =
  let ids = term_refs env t in
  let al = List.map (fun id -> (id, at_id id l)) (Idset.elements ids) in
  subst_in_term al t

(*s shortcuts for typing information *)

let effect p = p.info.kappa.c_effect
let pre p = p.info.kappa.c_pre
let post p = p.info.kappa.c_post
let result_type p = p.info.kappa.c_result_type


(*s [apply_pre] and [apply_post] instantiate pre- and post- conditions
    according to a given renaming of variables (and a date that means
    `before' in the case of the post-condition). *)

let make_assoc_list before ren env ids =
  Idset.fold
    (fun id al ->
       if is_reference env id then
	 (id, current_var ren id) :: al
       else if is_at id then
	 let uid,d = un_at id in
	 if is_reference env uid then begin
	   let d' = match d, before with
	     | "", None -> assert false
	     | "", Some l -> l
	     | _ -> d
	   in
	   (id, var_at_date ren d' uid) :: al
	 end else
	   al
       else
	 al) 
    ids []

let apply_term ren env t =
  let ids = term_vars t in
  let al = make_assoc_list None ren env ids in
  subst_in_term al t

let apply_pre ren env c =
  let ids = predicate_vars c.p_value in
  let al = make_assoc_list None ren env ids in
  { p_assert = c.p_assert; p_name = c.p_name; 
    p_value = subst_in_predicate al c.p_value }

let apply_assert ren env c =
  let ids = predicate_vars c.a_value in
  let al = make_assoc_list None ren env ids in
  { a_name = c.a_name; a_value = subst_in_predicate al c.a_value }
 
let apply_post before ren env c =
  let ids = predicate_vars c.a_value in
  let al = make_assoc_list (Some before) ren env ids in
  { a_name = c.a_name; a_value = subst_in_predicate al c.a_value }
  
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
  update empty_ren "0" ids


(*s Occurrences *)

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
  let n = Ident.bound () in
  let p = tsubst_in_predicate [x, Tbound n] p in
  Forall (x, n, mlize_type v, p)

let foralls =
  List.fold_right
    (fun (x,v) p -> if occur_predicate x p then forall x v p else p)
    
(*s Substitutions *)

let rec type_c_subst s c =
  let {c_result_name=id; c_result_type=t; c_effect=e; c_pre=p; c_post=q} = c in
  let s' = s @ List.map (fun (x,x') -> (at_id x "", at_id x' "")) s in
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
  | [] -> invalid_arg "make_arrow: no binder"
  | _ -> Arrow (bl,c)

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
      let ctrue = tsubst_in_predicate [Ident.result,ttrue] c in
      let cfalse = tsubst_in_predicate [Ident.result,tfalse] c in
      ctrue, cfalse
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
  Pand (le (Tconst (ConstInt 0)) c, lt c size)
      
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
  | App (p, a, None) -> 
      fprintf fmt "(@[%a@ %a@])" print_prog p print_arg a
  | App (p, a, Some k) -> 
      fprintf fmt "(@[%a %a ::@ %a@])" print_prog p print_arg a print_type_c k
  | LetRef (id, p1, p2) ->
      fprintf fmt "let %a = %a in %a" 
	Ident.print id print_prog p1 print_prog p2
  | LetIn (id, p1, p2) ->
      fprintf fmt "let %a = ref %a in %a" 
	Ident.print id print_prog p1 print_prog p2
  | Rec (id, bl, v, var, p) ->
      fprintf fmt "rec %a : <bl> %a { variant _ } =@\n%a" 
	Ident.print id print_type_v v print_prog p
  | Expression t -> 
      print_term fmt t
  | Coerce p ->
      print_prog fmt p

and print_block fmt = 
  print_list (fun fmt () -> fprintf fmt ";@\n") print_block_st fmt

and print_block_st fmt = function
  | Statement p -> print_prog fmt p
  | Label l -> fprintf fmt "label %s" l
  | Assert a -> fprintf fmt "assert {%a}" print_assertion a

and print_arg fmt = function
  | Refarg (_,r) -> Ident.print fmt r
  | Term p -> print_prog fmt p
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
      fprintf fmt "{%a | %a}" print_tuple bl print_predicate q

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
  | CC_lam (bl,c) ->
      fprintf fmt "@[<hov 2>";
      print_binders fmt bl;
      fprintf fmt "@,"; print_cc_term fmt c; fprintf fmt "@]"
  | CC_app (f,args) ->
      fprintf fmt "@[<hov 2>(%a@ %a)@]" 
      print_cc_term f (print_list pp_print_space print_cc_term) args
  | CC_tuple cl ->
      fprintf fmt "@[<hov 2>(%a)@]" (print_list comma print_cc_term) cl
  | CC_case (b,[bl1,e1; bl2,e2]) ->
      let branch bl e =
	print_binders fmt bl; fprintf fmt "@,"; print_cc_term fmt e in
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (branch bl1) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (branch bl2) e2;
      fprintf fmt "@]"
  | CC_case _ ->
      fprintf fmt "<Case...>"
  | CC_if (b,e1,e2) ->
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (print_cc_term fmt) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (print_cc_term fmt) e2;
      fprintf fmt "@]"
  | CC_expr c ->
      fprintf fmt "@["; print_term fmt c; fprintf fmt "@]"
  | CC_hole c ->
      fprintf fmt "@[(?:@ "; print_predicate fmt c; fprintf fmt ")@]"
  | CC_type t ->
      print_cc_type fmt t

and print_binders fmt bl =
  print_list nothing (fun fmt b -> fprintf fmt "[%a]" print_binder b) fmt bl
