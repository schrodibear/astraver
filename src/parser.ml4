
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: parser.ml4,v 1.1 2001-08-15 21:11:14 filliatr Exp $ *)

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
let pure_type= gec "pure_type"
let type_v   = gec "type_v"
let type_v0  = gec "type_v0"
let type_v1  = gec "type_v1"
let type_v2  = gec "type_v2"
let type_v3  = gec "type_v3"
let type_v_app  = gec "type_v_app"
let type_c   = gec "type_c"
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
let arg = gec "arg"
let block = gec "block"
let block_statement = gec "block_statement"
let relation = gec "relation"
let ident = gec "ident"
let wf_arg = gec "wf_arg"
let invariant = gec "invariant"
let variant = gec "variant"
let assertion = gec "assertion"
let precondition = gec "precondition"
let postcondition = gec "postcondition"
let predicate = gec "predicate"
let name = gec "name"

(*i
let ast_of_int n =
  G_zsyntax.z_of_string true n Ast.dummy_loc

let constr_of_int n =
  Astterm.interp_constr Evd.empty (Global.env ()) (ast_of_int n)

let ast_constant loc s = <:ast< (QUALID ($VAR $s)) >>
i*)

let conj_assert {a_name=n; a_value=a} {a_value=b} = 
  { a_value = Pand (a,b); a_name = n }

let conj = function
  | None,None     -> None
  | None,b        -> b
  | a,None        -> a
  | Some a,Some b -> Some (conj_assert a b)

let without_effect loc d = 
  { desc = d; pre = []; post = None; loc = loc; info = () }

let bin_op op loc e1 e2 =
  without_effect loc
    (App (without_effect loc (Expression (Tapp (op,[]))), [Term e1; Term e2]))

let un_op op loc e =
  without_effect loc
    (App (without_effect loc (Expression (Tapp (op,[]))), [Term e]))

let bool_bin op loc a1 a2 =
  let w = without_effect loc in
  let d = SApp ([Var op], [a1; a2]) in
  w d

let bool_or  loc = bool_bin Ident.p_or loc
let bool_and loc = bool_bin Ident.p_and loc

let bool_not loc a =
  let w = without_effect loc in
  let d = SApp ([Var Ident.p_not ], [a]) in
  w d

let zwf_zero = Tapp (Ident.t_zwf_zero, [])

(*i program -> Coq AST

let bdize c = 
  let env = 
    Global.env_of_context (Pcicenv.cci_sign_of Rename.empty_ren Env.empty)
  in
  Termast.ast_of_constr true env c

let rec coqast_of_program loc = function
  | Var id -> let s = string_of_id id in <:ast< ($VAR $s) >>
  | Acc id -> let s = string_of_id id in <:ast< ($VAR $s) >>
  | App (f,l) -> 
      let f = coqast_of_program f.loc f.desc in
      let args = List.map 
		   (function Term t -> coqast_of_program t.loc t.desc
		      | _ -> invalid_arg "coqast_of_program") l
      in
      <:ast< (APPLIST $f ($LIST $args)) >>
  | Expression c -> bdize c
  | _ -> invalid_arg "coqast_of_program"

(* The construction `for' is syntactic sugar.
 *
 * for i = v1 to v2 do { invariant Inv } block done
 *
 * ==> (let rec f i { variant v2+1-i } = 
 *        { i <= v2+1 /\ Inv(i) }
 *        (if i > v2 then tt else begin block; (f (i+1)) end) 
 *        { Inv(v2+1) }
 *      in (f v1)) { Inv(v2+1) }
 *)

let ast_plus_un loc ast =
  let zplus = ast_constant loc "Zplus" in
  let un = ast_of_int "1" in
  <:ast< (APPLIST $zplus $ast $un) >>

let make_ast_for loc i v1 v2 inv block =
  let f = for_name() in
  let id_i = id_of_string i in
  let var_i = without_effect loc (Var id_i) in
  let var_f = without_effect loc (Var f) in
  let succ_v2 = 
    let a_v2 = coqast_of_program v2.loc v2.desc in
    ast_plus_un loc a_v2 in
  let post = named_app (subst_ast_in_ast [ id_i, succ_v2 ]) inv in
  let e1 =
    let test = bin_op "Z_gt_le_bool" loc var_i v2 in
    let br_t = without_effect loc (Expression (constant "tt")) in
    let br_f = 
      let un = without_effect loc (Expression (constr_of_int "1")) in
      let succ_i = bin_op "Zplus" loc var_i un in
      let f_succ_i = without_effect loc (App (var_f, [Term succ_i])) in
      without_effect loc (Seq (block @ [Statement f_succ_i]))
    in
    let inv' = 
      let zle = ast_constant loc "Zle" in
      let i_le_sv2 = <:ast< (APPLIST $zle ($VAR $i) $succ_v2) >> in
      conj_assert {a_value=i_le_sv2;a_name=inv.a_name} inv
    in
    { desc = If(test,br_t,br_f); loc = loc; 
      pre = [pre_of_assert false inv']; post = Some post; info = () } 
  in
  let bl = 
    let typez = ast_constant loc "Z" in
    [(id_of_string i, BindType (PureType typez))] 
  in
  let fv1 = without_effect loc (App (var_f, [Term v1])) in
  let v = PureType (ast_constant loc "unit") in
  let var = 
    let zminus = ast_constant loc "Zminus" in
    let a = <:ast< (APPLIST $zminus $succ_v2 ($VAR $i)) >> in
    (a, ast_zwf_zero loc)
  in
  LetIn (f, without_effect loc (LetRec (f,bl,v,var,e1)), fv1)
i*)

let mk_prog loc p pre post =
  { desc = p.desc; 
    pre = p.pre @ pre; 
    post = conj (p.post,post); 
    loc = loc; 
    info = () }

EXTEND 

  ident:
  [ [ id = LIDENT -> Ident.create id
    | id = UIDENT -> Ident.create id ] ]
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
    | a = term1 -> a ] ]
  ;
  term1:
  [ [ "-"; a = term -> Tapp (Ident.t_neg, [a])
    | c = constant -> Tconst c
    | x = ident -> Tvar x
    | x = ident; "("; l = LIST1 term SEP ","; ")" -> Tapp (x,l) 
    | "("; a = term; ")" -> a ] ]
  ;
  constant:
  [ [ n = INT -> ConstInt (int_of_string n)
    | "true" -> ConstBool true
    | "false" -> ConstBool false
    | "void" -> ConstUnit
    | f = FLOAT -> ConstFloat (float_of_string f) ] ]
  ;
  predicate:
  [ [ a = predicate; "->"; b = predicate0 -> Pimplies (a,b)
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
  [ [ x = ident -> Pvar x
    | x = ident; "("; l = LIST1 term SEP ","; ")" -> Papp (x,l)
    | t1 = term; r = relation; t2 = term -> Papp (r, [t1;t2])
    | "not"; a = predicate -> Pnot a
    | "("; a = predicate; ")" -> a ] ] 
  ;

  (* Types *)
  pure_type:
    [ [ LIDENT "int" -> PTint
      | LIDENT "bool" -> PTbool
      | LIDENT "float" -> PTfloat
      | LIDENT "unit" -> PTunit
      | id = ident -> PTexternal id ] ] 
  ;    

  type_v:
    [ [ t = type_v0 -> t ] ]
  ;
  type_v0:
    [ [ t = type_v1 -> t ] ]
  ;
  type_v1:
    [ [ t = type_v2 -> t ] ]
  ;
  type_v2:
    [ LEFTA
      [ v = type_v2; LIDENT "ref" -> Ref v
      | t = type_v3 -> t ] ]
  ;
  type_v3:
    [ [ LIDENT "array"; size = term; "of"; v = type_v0 -> Array (size,v)
      | LIDENT "fun"; bl = binders; c = type_c -> make_arrow bl c
      | c = pure_type -> PureType c ] ]
  ;
  type_c:
    [ [ LIDENT "returns"; id = ident; ":"; v = type_v;
        e = effects; p = OPT pre_condition; q = OPT post_condition; "end" ->
        { c_result = (id, v);
	  c_effect = e;
	  c_pre = list_of_some p;
	  c_post = q } ] ] 
  ;
  effects:
    [ [ r = OPT reads; w = OPT writes ->
	let r' = match r with Some l -> l | _ -> [] in
	let w' = match w with Some l -> l | _ -> [] in
	List.fold_left (fun e x -> Effect.add_write x e)
	  (List.fold_left (fun e x -> Effect.add_read x e) Effect.bottom r')
          w'
      ] ]
  ;
  reads:
    [ [ LIDENT "reads"; l = LIST0 ident SEP "," -> l ] ]
  ;
  writes:
    [ [ LIDENT "writes"; l=LIST0 ident SEP "," -> l ] ]
  ;
  pre_condition:
    [ [ LIDENT "pre"; c = assertion -> pre_of_assert false c ] ]
  ;
  post_condition:
    [ [ LIDENT "post"; c = assertion -> c ] ]
  ;

  (* Binders (for both types and programs) **********************************)
  binder:
    [ [ "("; sl = LIST1 ident SEP ","; ":"; t = binder_type ; ")" ->
	  List.map (fun s -> (s, t)) sl
      ] ]
  ;
  binder_type:
    [ [ "Set" -> BindSet
      | v = type_v -> BindType v
      ] ]
  ;
  binders:
    [ [ bl = LIST0 binder -> List.flatten bl ] ] 
  ;

  (* Programs ***************************************************************)
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
    [ [ x = prog2; LIDENT "or"; y = prog1  -> bool_or loc x y
      | x = prog2; LIDENT "and"; y = prog1 -> bool_and loc x y
      | x = prog2 -> x
      ] ]
  ;
  ast2:
    [ [ LIDENT "not"; x = prog3 -> bool_not loc x
      | x = prog3 -> x
      ] ]
  ;
  ast3:
    [ [ x = prog4; rel = relation; y = prog4 -> bin_op rel loc x y
      | x = prog4 -> x
      ] ]
    ;
  ast4:
    [ [ x = prog5; "+"; y = prog4 -> bin_op Ident.t_add loc x y
      | x = prog5; "-"; y = prog4 -> bin_op Ident.t_sub loc x y
      | x = prog5 -> x
      ] ]
    ;
  ast5:
  [ [ x = prog6; "*"; y = prog5 -> bin_op Ident.t_mul loc x y 
    | x = prog6; "*"; y = prog5 -> bin_op Ident.t_mul loc x y 
    | x = prog6 -> x ] ]
  ;
  ast6:
  [ [ "-"; x = prog6 -> un_op Ident.t_neg loc x
    | x = ast7 -> without_effect loc x ] ]
  ;
  ast7:
  [ [ v = ident -> 
	Var v
    | n = INT ->
	Expression (Tconst (ConstInt (int_of_string n)))
    | "!"; v = ident ->
	Acc v
(*i | "?" -> isevar i*)
    | v = ident; ":="; p = program ->
	Aff (v,p)
    | v = ident; "["; e = program; "]" -> TabAcc (true,v,e)
    | v = ident; "#"; "["; e = program; "]" -> TabAcc (true,v,e)
    | v = ident; "["; e = program; "]"; ":="; p = program -> 
	TabAff (true,v,e,p)
    | v = ident; "#"; "["; e = program; "]"; ":="; p = program -> 
	TabAff (true,v,e,p)
    | "if"; e1 = program; "then"; e2 = program; "else"; e3 = program ->
	If (e1,e2,e3)
    | "if"; e1 = program; "then"; e2 = program ->
	If (e1,e2,without_effect loc (Expression (Tconst ConstUnit)))
    | "while"; b = program; "do"; 
	"{"; inv = OPT invariant; LIDENT "variant"; wf = variant; "}";
	bl = block; "done" ->
	  While (b, inv, wf, bl)
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
    | "let"; IDENT "rec"; f = ident; bl = binders; ":"; v = type_v;
	"{"; LIDENT "variant"; var = variant; "}"; "="; p = program ->
	  LetRec (f,bl,v,var,p)
    | "let"; "rec"; f = ident; bl = binders; ":"; v = type_v;
	"{"; LIDENT "variant"; var = variant; "}"; "="; p = program;
 	"in"; p2 = program ->
	  LetIn (f, without_effect loc (LetRec (f,bl,v,var,p)), p2)
	    
    | "@"; s = STRING; p = program ->
	Debug (s,p)
	  
    | "("; p = program; args = LIST0 arg; ")" ->
	match args with 
	  | [] -> 
	      if p.pre<>[] or p.post<>None then
		warning "Some annotations are lost";
	      p.desc
          | _  -> 
	      App(p,args)
    ] ]
  ;
  arg:
  [ [ "'"; t = type_v -> Type t
    | p = program -> Term p ] ]
  ;
  block:
  [ [ s = block_statement; ";"; b = block -> s::b
    | s = block_statement                 -> [s] ] ]
  ;
  block_statement:
    [ [ LIDENT "label"; s = IDENT -> Label s
      | LIDENT "assert"; "{"; c = assertion; "}" -> Assert c 
      | p = program -> Statement p ] ]
  ;
  relation:
    [ [ "<"  -> Ident.t_lt
      | "<=" -> Ident.t_le
      | ">"  -> Ident.t_gt
      | ">=" -> Ident.t_ge
      | "="  -> Ident.t_eq
      | "<>" -> Ident.t_noteq ] ] 
  ;

  (* Other entries (invariants, etc.) ***************************************)
  wf_arg:
  [ [ "{"; LIDENT "wf"; c = term; "for"; w = term; "}" -> Wf (c,w)
    | "{"; LIDENT "wf"; n = INT; "}" ->	RecArg (int_of_string n) ] ]
  ;
  invariant:
  [ [ LIDENT "invariant"; c = assertion -> c ] ]
  ;
  variant:
  [ [ c = term; "for"; r = term -> (c, r)
    | c = term -> (c, zwf_zero) ] ]
  ;
  END
;;

(*i

let is_assumed global ids =
  if List.length ids = 1 then
    mSGNL [< 'sTR (if global then "A global variable " else ""); 
	     pr_id (List.hd ids); 'sTR " is assumed" >]
  else
    mSGNL [< 'sTR (if global then "Some global variables " else "");
	     prlist_with_sep (fun () -> [< 'sTR ", " >]) pr_id ids;
	     'sTR " are assumed" >]

let _ = add "PROGDEBUGON"
     (function [] -> fun () -> debug := true | _  -> assert false)

let _ = add "PROGDEBUGOFF"
     (function [] -> fun () -> debug := false | _  -> assert false)

let _ = add "CORRECTNESS"
     (function
	 [ VARG_STRING s; VARG_DYN d ] -> 
	   fun () -> Ptactic.correctness s (out_prog d) None
       | [ VARG_STRING s; VARG_DYN d; VARG_TACTIC t ] ->
	   let tac = Tacinterp.interp t in
	   fun () -> Ptactic.correctness s (out_prog d) (Some tac)
       | _ -> assert false)

let _ = 
  add "SHOWPROGRAMS"
    (function
       | [] -> 
	   (fun () ->
	      fold_all 
		(fun (id,v) _ -> 
		   mSGNL [< pr_id id; 'sTR " : "; 
			    hOV 2 (match v with TypeV v -> pp_type_v v
				     | Set -> [< 'sTR "Set" >]);
			    'fNL >])
		Env.empty ())
       | _ -> assert false)

let id_of_varg = function VARG_IDENTIFIER id -> id | _ -> assert false
    
let _ = 
  add "PROGVARIABLE"
    (function
       | [ VARG_VARGLIST l; VARG_DYN d ] ->
	   (fun () ->
	      let ids = List.map id_of_varg l in
	      List.iter
		(fun id -> if Env.is_global id then
		   Util.errorlabstrm "PROGVARIABLE"
		     [< 'sTR"Clash with previous constant "; pr_id id >])
		ids;
	      let v = Pdb.db_type_v [] (out_typev d) in
	      let env = empty in
	      let ren = update empty_ren "" [] in
	      let v = Ptyping.cic_type_v env ren v in
	      if not (is_mutable v) then begin
		let c = trad_ml_type_v ren env v in
		List.iter 
		  (fun id -> ignore (Declare.declare_parameter id c)) ids;
		if_verbose (is_assumed false) ids
	      end;
	      if not (is_pure v) then begin
		List.iter (fun id -> ignore (Env.add_global id v None)) ids;
		if_verbose (is_assumed true) ids
	      end)
       | _ -> assert false)

open Vernac

GEXTEND Gram
  Pcoq.Vernac_.vernac:
  [ [ IDENT "Global"; "Variable"; 
      l = LIST1 IDENT SEP ","; ":"; t = type_v; "." ->
	let idl = List.map Ast.nvar l in
	let d = Ast.dynamic (in_typev t) in
	  <:ast< (PROGVARIABLE (VERNACARGLIST ($LIST $idl)) (VERNACDYN $d)) >>

    | IDENT "Show"; IDENT "Programs"; "." ->
	<:ast< (SHOWPROGRAMS) >>

    | IDENT "Correctness"; s = IDENT; p = Programs.program; "." ->
	let d = Ast.dynamic (in_prog p) in
	let str = Ast.str s in
	<:ast< (CORRECTNESS $str (VERNACDYN $d)) >>

    | IDENT "Correctness"; s = IDENT; p = Programs.program; ";";
      tac = Tactic.tactic; "." ->
	let d = Ast.dynamic (in_prog p) in
	let str = Ast.str s in
	<:ast< (CORRECTNESS $str (VERNACDYN $d) (TACTIC $tac)) >>

    | IDENT "Debug"; IDENT "on"; "." -> <:ast< (PROGDEBUGON) >>
	
    | IDENT "Debug"; IDENT "off"; "." -> <:ast< (PROGDEBUGOFF) >>
	    
  ] ]
  ;
 END
;;

i*)
