(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.ml4,v 1.43 2002-07-05 16:14:09 filliatr Exp $ i*)

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
let predicate3 = gec "predicate3"
let predicate4 = gec "predicate4"
let predicate5 = gec "predicate5"
let predicate6 = gec "predicate6"
let predicate7 = gec "predicate7"
let pp_relation = gec "pp_relation"
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
let raises   = gec "raises"
let cast     = gec "cast"
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
let exception_type = gec "exception_type"
let assertion = gec "assertion"
let precondition = gec "precondition"
let postcondition = gec "postcondition"
let predicate = gec "predicate"
let name = gec "name"

let decl = gec "decl"
let decls = gec "decls"
let logic_type = gec "logic_type"
let logic_arg = gec "logic_arg"


(*s Utility functions. *)

let mk_pp loc d = { pp_loc = loc; pp_desc = d }
let infix_pp loc a i b = mk_pp loc (PPinfix (a, i, b))
let prefix_pp loc p a = mk_pp loc (PPprefix (p, a))

let conj_assert {a_name=n; a_value=a} {a_value=b} = 
  { a_value = infix_pp (Loc.join a.pp_loc b.pp_loc) a PPand b; a_name = n }

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
	Ident.at_id id ""
    | id = ident; "@"; l = ident -> 
	Ident.at_id id (Ident.string l) ] ]
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
    | a = term0; "%"; b = term1 -> Tapp (Ident.t_mod, [a;b])
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
  [ [ a = predicate0; "->"; b = predicate -> infix_pp loc a PPimplies b
    | a = predicate0 -> a ] ]
  ; 
  predicate0:
  [ [ a = predicate0; "or"; b = predicate1 -> infix_pp loc a PPor b
    | a = predicate1 -> a ] ]
  ; 
  predicate1:
  [ [ a = predicate1; "and"; b = predicate2 -> infix_pp loc a PPand b
    | a = predicate2 -> a ] ]
  ;
  predicate2:
  [ [ "not"; a = predicate3 -> prefix_pp loc PPnot a
    | a = predicate3 -> a ] ]
  ;
  predicate3:
  [ [ a = predicate4; r = pp_relation; b = predicate4 -> 
	infix_pp loc a r b
    | a = predicate4; r1 = pp_relation; b = predicate4;
      r2 = pp_relation; c = predicate4 -> 
	infix_pp loc (infix_pp loc a r1 b) PPand (infix_pp loc b r2 c)
    | a = predicate4 -> 
	a ] ]
  ;
  predicate4:
  [ [ a = predicate5; "+"; b = predicate4 -> infix_pp loc a PPadd b
    | a = predicate5; "-"; b = predicate4 -> infix_pp loc a PPsub b
    | a = predicate5 -> a ] ]
  ;
  predicate5:
  [ [ a = predicate6; "*"; b = predicate5 -> infix_pp loc a PPmul b
    | a = predicate6; "/"; b = predicate5 -> infix_pp loc a PPdiv b
    | a = predicate6; "%"; b = predicate5 -> infix_pp loc a PPmod b
    | a = predicate6 -> a ] ]
  ;
  predicate6:
  [ [ "-"; a = predicate6 -> prefix_pp loc PPneg a
    | a = predicate7 -> a ] ]
  ;
  predicate7:
  [ [ "true" -> 
	mk_pp loc PPtrue
    | "false" -> 
	mk_pp loc PPfalse
    | c = constant ->
	mk_pp loc (PPconst c)
(*** make result a keyword?
    | LIDENT "result" ->
	mk_pp loc (PPvar Ident.result)
***)
    | x = qualid_ident ->
	mk_pp loc (PPvar x)
    | x = qualid_ident; "("; l = LIST1 predicate SEP ","; ")" -> 
	mk_pp loc (PPapp (x,l))
    | x = qualid_ident; "["; t = predicate; "]" -> 
	mk_pp loc (PPapp (Ident.access, [mk_pp loc (PPvar x); t]))
    | "if"; p0 = predicate; "then"; p1 = predicate; "else"; p2 = predicate ->
	mk_pp loc (PPif (p0, p1, p2))
    | LIDENT "forall"; id = ident; ":"; t = primitive_type; 
      "." ; a = predicate -> 
	mk_pp loc (PPforall (id, t, a))
    | "("; a = predicate; ")" -> 
	a ] ] 
  ;
  pp_relation:
  [ [ "<" -> PPlt
    | "<=" -> PPle
    | ">" -> PPgt
    | ">=" -> PPge
    | "=" -> PPeq
    | "<>" -> PPneq ] ]
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
	Arrow ([Ident.anonymous, BindType v], c)
    | x = LIDENT; ":"; v = simple_type_v; "->"; c = type_c -> 
	Arrow ([(Ident.create x, BindType v)], c)
    | x = UIDENT; ":"; v = simple_type_v; "->"; c = type_c -> 
	Arrow ([(Ident.create x, BindType v)], c)
    | t = simple_type_v -> 
	t ] ]
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
  [ [ r = OPT reads; w = OPT writes; x = OPT raises ->
      let r' = match r with Some l -> l | _ -> [] in
      let w' = match w with Some l -> l | _ -> [] in
      let x' = match x with Some l -> l | _ -> [] in
      List.fold_right Effect.add_write w'
	(List.fold_right Effect.add_read r' 
	   (List.fold_right Effect.add_exn x' Effect.bottom))
    ] ]
  ;
  reads:
  [ [ LIDENT "reads"; l = LIST0 ident SEP "," -> l ] ]
  ;
  writes:
  [ [ LIDENT "writes"; l = LIST0 ident SEP "," -> l ] ]
  ;
  raises:
  [ [ LIDENT "raises"; l = LIST0 ident SEP "," -> l ] ]
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
  [ [ "-"; x = prog6 -> un_op Ident.t_neg_int loc x
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
    | "raise"; id = ident; t = OPT cast ->
	Raise (id, None, t)
    | "raise"; "("; id = ident; p = program; ")"; t = OPT cast ->
	Raise (id, Some p, t)
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
  cast:
  [ [ ":"; t = type_v -> t ] ]
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
  [ [ c = term; "for"; r = term -> (c, PTint, r)
    | c = term; ":"; t = primitive_type; "for"; r = term -> (c, t, r)
    | c = term -> (c, PTint, zwf_zero) ] ]
  ;
  exception_type:
  [ [ "of"; v = primitive_type -> v ] ]
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
    | "exception"; id = ident; v = OPT exception_type ->
	Exception (loc, id, v)
    | "logic"; id = ident; ":"; t = logic_type ->
	Logic (loc, id, t)
    | LIDENT "pvs"; s = STRING ->
        QPvs s ] ]
  ;
  decls: 
  [ [ d = LIST0 decl; EOI -> d ] ]
  ;
  logic_type:
  [ [ b = LIST1 logic_arg SEP ","; "->"; LIDENT "prop" -> Predicate b
    | b = LIST1 logic_arg SEP ","; "->"; t = primitive_type -> Function (b,t)
  ] ]
  ;	
  logic_arg:
  [ [ t = primitive_type -> t
    | "array"; t = primitive_type -> PTarray (Tvar Ident.implicit, t)
  ] ]
  ;
END
;;

