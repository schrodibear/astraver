(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.ml4,v 1.51 2002-07-19 13:01:36 filliatr Exp $ i*)

open Logic
open Rename
open Misc
open Util
open Types
open Ptree
open Env

let gram = Grammar.create (Plexer.make ())
let gec s = Grammar.Entry.create gram s

(* logic *)
let lexpr = gec "lexpr"
let lexpr0 = gec "lexpr0"
let lexpr1 = gec "lexpr1"
let lexpr2 = gec "lexpr2"
let lexpr3 = gec "lexpr3"
let lexpr4 = gec "lexpr4"
let lexpr5 = gec "lexpr5"
let lexpr6 = gec "lexpr6"
let lexpr7 = gec "lexpr7"
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
let lexpr = gec "lexpr"
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
  { pdesc = d; pre = []; post = None; loc = loc }

let rec app f = function
  | [] -> 
      assert false
  | [a] -> 
      Sapp (f, a)
  | a :: l -> 
      let loc = Loc.join f.loc (arg_loc a) in 
      app (without_annot loc (Sapp (f, a))) l

let bin_op op loc e1 e2 =
  without_annot loc
    (app (without_annot loc (Svar op)) [Sterm e1; Sterm e2])

let un_op op loc e =
  without_annot loc
    (app (without_annot loc (Svar op)) [Sterm e])

let bool_not loc a = un_op Ident.p_not loc a

let mk_prog loc p pre post =
  { pdesc = p.pdesc; 
    pre = p.pre @ pre; 
    post = conj (p.post, post); 
    loc = loc }

let rec_name = function Srec (x,_,_,_,_) -> x | _ -> assert false

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
  constant:
  [ [ n = INT -> ConstInt (int_of_string n)
    | "true" -> ConstBool true
    | "false" -> ConstBool false
    | LIDENT "void" -> ConstUnit
    | f = FLOAT -> ConstFloat f ] ]
  ;
  lexpr:
  [ [ a = lexpr0; "->"; b = lexpr -> infix_pp loc a PPimplies b
    | a = lexpr0 -> a ] ]
  ; 
  lexpr0:
  [ [ a = lexpr0; "or"; b = lexpr1 -> infix_pp loc a PPor b
    | a = lexpr1 -> a ] ]
  ; 
  lexpr1:
  [ [ a = lexpr1; "and"; b = lexpr2 -> infix_pp loc a PPand b
    | a = lexpr2 -> a ] ]
  ;
  lexpr2:
  [ [ "not"; a = lexpr3 -> prefix_pp loc PPnot a
    | a = lexpr3 -> a ] ]
  ;
  lexpr3:
  [ [ a = lexpr4; r = pp_relation; b = lexpr4 -> 
	infix_pp loc a r b
    | a = lexpr4; r1 = pp_relation; b = lexpr4;
      r2 = pp_relation; c = lexpr4 -> 
	infix_pp loc (infix_pp loc a r1 b) PPand (infix_pp loc b r2 c)
    | a = lexpr4 -> 
	a ] ]
  ;
  lexpr4:
  [ [ a = lexpr4; "+"; b = lexpr5 -> infix_pp loc a PPadd b
    | a = lexpr4; "-"; b = lexpr5 -> infix_pp loc a PPsub b
    | a = lexpr5 -> a ] ]
  ;
  lexpr5:
  [ [ a = lexpr5; "*"; b = lexpr6 -> infix_pp loc a PPmul b
    | a = lexpr5; "/"; b = lexpr6 -> infix_pp loc a PPdiv b
    | a = lexpr5; "%"; b = lexpr6 -> infix_pp loc a PPmod b
    | a = lexpr6 -> a ] ]
  ;
  lexpr6:
  [ [ "-"; a = lexpr6 -> prefix_pp loc PPneg a
    | a = lexpr7 -> a ] ]
  ;
  lexpr7:
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
    | x = qualid_ident; "("; l = LIST1 lexpr SEP ","; ")" -> 
	mk_pp loc (PPapp (x,l))
    | x = qualid_ident; "["; t = lexpr; "]" -> 
	mk_pp loc (PPapp (Ident.access, [mk_pp loc (PPvar x); t]))
    | "if"; p0 = lexpr; "then"; p1 = lexpr; "else"; p2 = lexpr ->
	mk_pp loc (PPif (p0, p1, p2))
    | LIDENT "forall"; id = ident; ":"; t = primitive_type; 
      "." ; a = lexpr -> 
	mk_pp loc (PPforall (id, t, a))
    | "("; a = lexpr; ")" -> 
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
	PVarrow ([Ident.anonymous, BindType v], c)
    | x = LIDENT; ":"; v = simple_type_v; "->"; c = type_c -> 
	PVarrow ([(Ident.create x, BindType v)], c)
    | x = UIDENT; ":"; v = simple_type_v; "->"; c = type_c -> 
	PVarrow ([(Ident.create x, BindType v)], c)
    | t = simple_type_v -> 
	t ] ]
  ;
  simple_type_v:
  [ [ "array"; size = lexpr; "of"; v = simple_type_v -> PVarray (size,v)
    | v = simple_type_v; "ref" -> PVref v
    | t = primitive_type -> PVpure t
    | "("; v = type_v; ")" -> v ] ] 
  ;
  type_c:
  [ [ "{"; p = OPT pre_condition; "}";
      (id,v) = result; e = effects; 
      "{"; q = OPT post_condition; "}" ->
        { pc_result_name = id; pc_result_type = v;
	  pc_effect = e; pc_pre = list_of_some p; pc_post = q } 
    | v = type_v -> 
	ptype_c_of_v v ] ] 
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
  [ [ c = lexpr; n = name -> { a_name = n; a_value = c } ] ]
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
       let ptrue = without_annot loc (Sconst (ConstBool true)) in
       without_annot loc (Sif (x, ptrue, y))
    | x = prog2; "&&"; y = prog1 -> 
       let pf = without_annot loc (Sconst (ConstBool false)) in
       without_annot loc (Sif (x, y, pf))
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
    | x = prog6; "%"; y = prog5 -> bin_op Ident.t_mod_int loc x y 
    | x = prog6 -> x ] ]
  ;
  ast6:
  [ [ "-"; x = prog6 -> un_op Ident.t_neg loc x
    | LIDENT "sqrt_float"; x = prog6 -> un_op Ident.t_sqrt_float loc x
    | x = ast7 -> without_annot loc x ] ]
  ;
  ast7:
  [ [ v = ident -> 
	Svar v
    | n = INT ->
	Sconst (ConstInt (int_of_string n))
    | f = FLOAT ->
	Sconst (ConstFloat f)
    | LIDENT "void" ->
	Sconst ConstUnit
    | "true" ->
	Sconst (ConstBool true)
    | "false" ->
	Sconst (ConstBool false)
    | "!"; v = ident ->
	Srefget v
    | v = ident; ":="; p = program ->
	Srefset (v,p)
    | v = ident; "["; e = program; "]" -> 
	Sarrget (true,v,e)
    | v = ident; "["; e = program; "]"; ":="; p = program -> 
	Sarrset (true,v,e,p)
    | "if"; e1 = program; "then"; e2 = program; "else"; e3 = program ->
	Sif (e1,e2,e3)
    | "if"; e1 = program; "then"; e2 = program ->
	Sif (e1,e2,without_annot loc (Sconst ConstUnit))
    | "while"; b = program; "do"; 
	"{"; inv = OPT invariant; LIDENT "variant"; wf = variant; "}";
	bl = block; "done" ->
	  Swhile (b, inv, wf, without_annot loc (Sseq bl))
(*i
    | "for"; i = ident; "="; v1 = program; "to"; v2 = program;
	"do"; "{"; inv = invariant; "}"; bl = block; "done" -> 
	  make_ast_for loc i v1 v2 inv bl
i*)
    | "let"; v = ident; "="; "ref"; p1 = program; "in"; p2 = program ->
	Sletref (v, p1, p2)
    | "let"; v = ident; "="; p1 = program; "in"; p2 = program ->
	Sletin (v, p1, p2)
    | "begin"; b = block; "end" ->
	Sseq b
    | "fun"; bl = binders; "->"; p = program ->
	Slam (bl,p)
    | "let"; "rec"; p = recfun -> 
        p
    | "let"; "rec"; p = recfun; "in"; p2 = program ->
	Sletin (rec_name p, without_annot loc p, p2)
    | "raise"; id = ident; t = OPT cast ->
	Sraise (id, None, t)
    | "raise"; "("; id = ident; p = program; ")"; t = OPT cast ->
	Sraise (id, Some p, t)
    | "("; p = program; args = LIST0 arg; ")" ->
	match args with 
	  | [] -> 
	      if p.pre <> [] || p.post <> None then
		warning "Some annotations are lost";
	      p.pdesc
          | _  -> 
	      app p args
    ] ]
  ;
  recfun:
  [ [ f = ident; bl = binders; ":"; v = type_v;
      "{"; LIDENT "variant"; var = variant; "}"; "="; p = program ->
	Srec (f,bl,v,var,p) ] ]
  ;
  arg:
  [ [ "'"; t = type_v -> Stype t
    | p = program -> Sterm p ] ]
  ;
  cast:
  [ [ ":"; t = type_v -> t ] ]
  ;
  block:
  [ [ s = block_statement; ";"; b = block -> s :: b
    | s = block_statement                 -> [s] ] ]
  ;
  block_statement:
    [ [ LIDENT "label"; s = ident -> Slabel (Ident.string s)
      | LIDENT "assert"; "{"; c = assertion; "}" -> Sassert c 
      | p = program -> Sstatement p ] ]
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
  [ [ c = lexpr; "for"; r = ident -> (c, r)
    | c = lexpr -> (c, Ident.t_zwf_zero) ] ]
  ;
  exception_type:
  [ [ "of"; v = primitive_type -> v ] ]
  ;

  (* declarations *)
  decl:
  [ [ "let"; id = ident; "="; p = program -> 
	Program (id, p)
    | "let"; id = ident; bl = binders; "="; p = program -> 
	Program (id, without_annot loc (Slam (bl, p)))
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

