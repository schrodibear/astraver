(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.ml4,v 1.35 2002-04-29 08:47:37 filliatr Exp $ i*)

open Logic
open Rename
open Misc
open Util
open Types
open Ast
open Env

let gram = Grammar.create (Plexer.make ())
let gec s = Grammar.Entry.create gram s

(* logic *)
let term = gec "term"
let term0 = gec "term0"
let term1 = gec "term1"
let predicate = gec "predicate"
let predicate0 = gec "predicate0"
let predicate1 = gec "predicate1"
let predicate2 = gec "predicate2"
let constant = gec "constant"

(* types *)
let primitive_type = gec "primitive_type"
let type_v   = gec "type_v"
let simple_type_v   = gec "simple_type_v"
let type_c   = gec "type_c"
let result   = gec "result"
let effects  = gec "effects"
let reads    = gec "reads"
let writes   = gec "writes"
let pre_condition = gec "pre_condition"
let post_condition = gec "post_condition"

(* binders *)
let binder  = gec "binder"
let binder_type = gec "binder_type"
let binders  = gec "binders"

(* programs *)
let program = gec "program"
let prog1 = gec "prog1"
let prog2 = gec "prog2"
let prog3 = gec "prog3"
let prog4 = gec "prog4"
let prog5 = gec "prog5"
let prog6 = gec "prog6"
let prog7 = gec "prog7"
let ast1 = gec "ast1"
let ast2 = gec "ast2"
let ast3 = gec "ast3"
let ast4 = gec "ast4"
let ast5 = gec "ast5"
let ast6 = gec "ast6"
let ast7 = gec "ast7"
let recfun = gec "recfun"
let arg = gec "arg"
let block = gec "block"
let block_statement = gec "block_statement"
let relation = gec "relation"
let ident = gec "ident"
let qualid_ident = gec "qualid_ident"
let invariant = gec "invariant"
let variant = gec "variant"
let assertion = gec "assertion"
let precondition = gec "precondition"
let postcondition = gec "postcondition"
let predicate = gec "predicate"
let name = gec "name"

let decl = gec "decl"
let decls = gec "decls"

(*s Utility functions. *)

let predicate_of_term loc = function
  | Tvar id -> Pvar id
  | Tapp (id, lt) -> Papp (id, lt)
  | Tconst _ -> raise (Stdpp.Exc_located (loc, 
					  Stream.Error "predicate expected"))

let conj_assert {a_name=n; a_value=a} {a_value=b} = 
  { a_value = Pand (a,b); a_name = n }

let conj = function
  | None,None     -> None
  | None,b        -> b
  | a,None        -> a
  | Some a,Some b -> Some (conj_assert a b)

let without_annot loc d = 
  { desc = d; info = { pre = []; post = None; loc = loc } }

let rec app f = function
  | [] -> 
      assert false
  | [a] -> 
      App (f, a, None)
  | a :: l -> 
      let loc = Loc.join f.info.loc (arg_loc a) in 
      app (without_annot loc (App (f, a, None))) l

let bin_op op loc e1 e2 =
  without_annot loc
    (app (without_annot loc (Var op)) [Term e1; Term e2])

let un_op op loc e =
  without_annot loc
    (app (without_annot loc (Expression (Tapp (op,[])))) [Term e])

let bool_not loc a = un_op Ident.p_not loc a

let zwf_zero = Tvar Ident.t_zwf_zero

let mk_prog loc p pre post =
  { desc = p.desc; 
    info = { pre = p.info.pre @ pre; 
	     post = conj (p.info.post, post); 
	     loc = loc } }

let rec_name = function Rec (x,_,_,_,_) -> x | _ -> assert false

EXTEND 

  ident:
  [ [ id = LIDENT -> Ident.create id
    | id = UIDENT -> Ident.create id ] ]
  ;
  qualid_ident:
  [ [ id = ident ->
	id
    | id = ident; "@" -> 
	Ident.create (Ident.string id ^ "@")
    | id = ident; "@"; l = ident -> 
	Ident.create (Ident.string id ^ "@" ^ Ident.string l) ] ]
  ;

  (* Logic *)
  term:
  [ [ a = term; "+"; b = term0 -> Tapp (Ident.t_add, [a;b])
    | a = term; "-"; b = term0 -> Tapp (Ident.t_sub, [a;b])
    | a = term0 -> a ] ]
  ;
  term0:
  [ [ a = term0; "*"; b = term1 -> Tapp (Ident.t_mul, [a;b])
    | a = term0; "/"; b = term1 -> Tapp (Ident.t_div, [a;b])
    | a = term0; "%"; b = term1 -> Tapp (Ident.t_div, [a;b])
    | a = term1 -> a ] ]
  ;
  term1:
  [ [ "-"; a = term1 -> Tapp (Ident.t_neg, [a])
    | c = constant -> Tconst c
    | x = qualid_ident -> Tvar x
    | x = qualid_ident; "("; l = LIST1 term SEP ","; ")" -> Tapp (x,l) 
    | x = qualid_ident; "["; t = term; "]" -> Tapp (Ident.access, [Tvar x; t])

    | "("; a = term; ")" -> a ] ]
  ;
  constant:
  [ [ n = INT -> ConstInt (int_of_string n)
    | "true" -> ConstBool true
    | "false" -> ConstBool false
    | LIDENT "void" -> ConstUnit
    | f = FLOAT -> ConstFloat (float_of_string f) ] ]
  ;
  predicate:
  [ [ a = predicate0; "->"; b = predicate -> Pimplies (a,b)
    | a = predicate0 -> a ] ]
  ; 
  predicate0:
  [ [ a = predicate0; "or"; b = predicate1 -> Por (a,b)
    | a = predicate1 -> a ] ]
  ; 
  predicate1:
  [ [ a = predicate1; "and"; b = predicate2 -> Pand (a,b)
    | a = predicate2 -> a ] ]
  ;
  predicate2:
  [ [ t = term -> predicate_of_term loc t
    | t1 = term; r = relation; t2 = term -> Papp (r, [t1;t2])
    | t1 = term; r1 = relation; t2 = term; r2 = relation; t3 = term ->
	Pand (Papp (r1, [t1;t2]), Papp (r2, [t2;t3]))
    | "if"; t = term; "then"; p1 = predicate; "else"; p2 = predicate ->
	Pif (t, p1, p2)
    | LIDENT "forall"; id = ident; ":"; t = primitive_type; 
      "." ; a = predicate -> forall id (PureType t) a 
    | "not"; a = predicate -> Pnot a
    | "true" -> Ptrue
    | "false" -> Pfalse
    | "("; a = predicate; ")" -> a ] ] 
  ;

  (* Types *)
  primitive_type:
  [ [ "int" -> PTint
    | "bool" -> PTbool
    | "float" -> PTfloat
    | "unit" -> PTunit 
    | id = ident -> PTexternal id ] ]
  ;
  (* [ident] is expansed to allow factorization *)
  type_v:
  [ [ v = simple_type_v; "->"; c = type_c -> 
	make_arrow [Ident.anonymous, BindType v] c
    | x = LIDENT; ":"; v = simple_type_v; "->"; c = type_c -> 
	make_arrow [(Ident.create x, BindType v)] c
    | x = UIDENT; ":"; v = simple_type_v; "->"; c = type_c -> 
	make_arrow [(Ident.create x, BindType v)] c
    | t = simple_type_v -> t ] ]
  ;
  simple_type_v:
  [ [ "array"; size = term; "of"; v = simple_type_v -> Array (size,v)
    | v = simple_type_v; "ref" -> Ref v
    | t = primitive_type -> PureType t
    | "("; v = type_v; ")" -> v ] ] 
  ;
  type_c:
  [ [ "{"; p = OPT pre_condition; "}";
      (id,v) = result; e = effects; 
      "{"; q = OPT post_condition; "}" ->
	let s = subst_onev id Ident.result in
	let q = optpost_app (subst_in_predicate s) q in
        { c_result_name = id; c_result_type = v;
	  c_effect = e; c_pre = list_of_some p; c_post = q } 
    | v = type_v -> 
	type_c_of_v v ] ] 
  ;
  result:
  [ [ LIDENT "returns"; id = ident; ":"; v = type_v -> (id, v)
    | v = type_v -> (Ident.result, v) ] ]
  ;
  effects:
  [ [ r = OPT reads; w = OPT writes ->
      let r' = match r with Some l -> l | _ -> [] in
      let w' = match w with Some l -> l | _ -> [] in
      List.fold_right Effect.add_write w'
	(List.fold_right Effect.add_read r' Effect.bottom)
    ] ]
  ;
  reads:
  [ [ LIDENT "reads"; l = LIST0 ident SEP "," -> l ] ]
  ;
  writes:
  [ [ LIDENT "writes"; l = LIST0 ident SEP "," -> l ] ]
  ;
  pre_condition:
  [ [ c = assertion -> pre_of_assert false c ] ]
  ;
  post_condition:
  [ [ c = assertion -> c ] ]
  ;

  (* Binders (for both types and programs) *)
  binder:
  [ [ "("; sl = LIST1 ident SEP ","; ":"; t = binder_type ; ")" ->
	List.map (fun s -> (s, t)) sl ] ]
  ;
  binder_type:
  [ [ UIDENT "Set" -> BindSet
    | v = type_v -> BindType v ] ]
  ;
  binders:
  [ [ bl = LIST1 binder -> List.flatten bl ] ] 
  ;

  (* Programs *)
  assertion:
  [ [ c = predicate; n = name -> { a_name = n; a_value = c } ] ]
  ;
  name:
  [ [ "as"; id = ident -> Ident.Name id
    | -> Ident.Anonymous ] ]
  ;

  precondition:
  [ [ "{"; c = assertion; "}" -> pre_of_assert false c ] ]
  ;
  postcondition:
  [ [ "{"; c = assertion; "}" -> c ] ]
  ;
  program:
  [ [ p = prog1 -> p ] ]
  ;
  prog1:
  [ [ pre = LIST0 precondition; ast = ast1; post = OPT postcondition ->
	mk_prog loc ast pre post ] ]
  ;
  prog2:
  [ [ pre = LIST0 precondition; ast = ast2; post = OPT postcondition ->
	mk_prog loc ast pre post ] ]
  ;
  prog3:
  [ [ pre = LIST0 precondition; ast = ast3; post = OPT postcondition ->
	mk_prog loc ast pre post ] ]
  ;
  prog4:
  [ [ pre = LIST0 precondition; ast = ast4; post = OPT postcondition ->
	mk_prog loc ast pre post ] ]
  ;
  prog5:
  [ [ pre = LIST0 precondition; ast = ast5; post = OPT postcondition ->
	mk_prog loc ast pre post ] ]
  ;
  prog6:
  [ [ pre = LIST0 precondition; ast = ast6; post = OPT postcondition ->
	mk_prog loc ast pre post ] ]
  ;

  ast1:
  [ [ x = prog2; "||"; y = prog1  -> 
       let ptrue = without_annot loc (Expression (Tconst (ConstBool true))) in
       without_annot loc (If (x, ptrue, y))
    | x = prog2; "&&"; y = prog1 -> 
       let pf = without_annot loc (Expression (Tconst (ConstBool false))) in
       without_annot loc (If (x, y, pf))
    | x = prog2 -> x ] ]
  ;
  ast2:
  [ [ LIDENT "not"; x = prog3 -> bool_not loc x
    | x = prog3 -> x ] ]
  ;
  ast3:
  [ [ x = prog4; rel = relation; y = prog4 -> bin_op rel loc x y
    | x = prog4 -> x ] ]
  ;
  ast4:
  [ [ x = prog5; "+"; y = prog4 -> bin_op Ident.t_add loc x y
    | x = prog5; "-"; y = prog4 -> bin_op Ident.t_sub loc x y
    | x = prog5 -> x ] ]
  ;
  ast5:
  [ [ x = prog6; "*"; y = prog5 -> bin_op Ident.t_mul loc x y 
    | x = prog6; "/"; y = prog5 -> bin_op Ident.t_div loc x y 
    | x = prog6; "%"; y = prog5 -> bin_op Ident.t_mod loc x y 
    | x = prog6 -> x ] ]
  ;
  ast6:
  [ [ "-"; x = prog6 -> un_op Ident.t_neg loc x
    | LIDENT "sqrt"; x = prog6 -> un_op Ident.t_sqrt loc x
    | x = ast7 -> without_annot loc x ] ]
  ;
  ast7:
  [ [ v = ident -> 
	Var v
    | n = INT ->
	Expression (Tconst (ConstInt (int_of_string n)))
    | f = FLOAT ->
	Expression (Tconst (ConstFloat (float_of_string f)))
    | LIDENT "void" ->
	Expression (Tconst ConstUnit)
    | "true" ->
	Expression (Tconst (ConstBool true))
    | "false" ->
	Expression (Tconst (ConstBool false))
    | "!"; v = ident ->
	Acc v
    | v = ident; ":="; p = program ->
	Aff (v,p)
    | v = ident; "["; e = program; "]" -> 
	TabAcc (true,v,e)
    | v = ident; "["; e = program; "]"; ":="; p = program -> 
	TabAff (true,v,e,p)
    | "if"; e1 = program; "then"; e2 = program; "else"; e3 = program ->
	If (e1,e2,e3)
    | "if"; e1 = program; "then"; e2 = program ->
	If (e1,e2,without_annot loc (Expression (Tconst ConstUnit)))
    | "while"; b = program; "do"; 
	"{"; inv = OPT invariant; LIDENT "variant"; wf = variant; "}";
	bl = block; "done" ->
	  While (b, inv, wf, without_annot loc (Seq bl))
(*i
    | "for"; i = ident; "="; v1 = program; "to"; v2 = program;
	"do"; "{"; inv = invariant; "}"; bl = block; "done" -> 
	  make_ast_for loc i v1 v2 inv bl
i*)
    | "let"; v = ident; "="; "ref"; p1 = program; "in"; p2 = program ->
	LetRef (v, p1, p2)
    | "let"; v = ident; "="; p1 = program; "in"; p2 = program ->
	LetIn (v, p1, p2)
    | "begin"; b = block; "end" ->
	Seq b
    | "fun"; bl = binders; "->"; p = program ->
	Lam (bl,p)
    | "let"; "rec"; p = recfun -> 
        p
    | "let"; "rec"; p = recfun; "in"; p2 = program ->
	LetIn (rec_name p, without_annot loc p, p2)
    | "("; p = program; args = LIST0 arg; ")" ->
	match args with 
	  | [] -> 
	      if p.info.pre <> [] || p.info.post <> None then
		warning "Some annotations are lost";
	      p.desc
          | _  -> 
	      app p args
    ] ]
  ;
  recfun:
  [ [ f = ident; bl = binders; ":"; v = type_v;
      "{"; LIDENT "variant"; var = variant; "}"; "="; p = program ->
	Rec (f,bl,v,var,p) ] ]
  ;
  arg:
  [ [ "'"; t = type_v -> Type t
    | p = program -> Term p ] ]
  ;
  block:
  [ [ s = block_statement; ";"; b = block -> s :: b
    | s = block_statement                 -> [s] ] ]
  ;
  block_statement:
    [ [ LIDENT "label"; s = ident -> Label (Ident.string s)
      | LIDENT "assert"; "{"; c = assertion; "}" -> Assert c 
      | p = program -> Statement p ] ]
  ;
  relation:
    [ [ "<"  -> Ident.t_lt
      | "<=" -> Ident.t_le
      | ">"  -> Ident.t_gt
      | ">=" -> Ident.t_ge
      | "="  -> Ident.t_eq
      | "<>" -> Ident.t_neq ] ] 
  ;

  (* Other entries (invariants, etc.) *)
  invariant:
  [ [ LIDENT "invariant"; c = assertion -> c ] ]
  ;
  variant:
  [ [ c = term; "for"; r = term -> (c, r)
    | c = term -> (c, zwf_zero) ] ]
  ;

  (* declarations *)
  decl:
  [ [ "let"; id = ident; "="; p = program -> 
	Program (id, p)
    | "let"; "rec"; p = recfun -> 
	Program (rec_name p, without_annot loc p)
    | "external"; ids = LIST1 ident SEP ","; ":"; v = type_v -> 
	External (loc, ids, v)
    | "parameter"; ids = LIST1 ident SEP ","; ":"; v = type_v -> 
	Parameter (loc, ids, v)
    | LIDENT "pvs"; s = STRING ->
        QPvs s ] ]
  ;
  decls: 
  [ [ d = LIST0 decl; EOI -> d ] ]
  ;
END
;;

