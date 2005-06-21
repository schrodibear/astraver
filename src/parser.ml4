(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: parser.ml4,v 1.103 2005-06-21 07:45:04 filliatr Exp $ i*)

open Options
open Logic
open Misc
open Util
open Types
open Ptree
open Compat

(*s Lexer. Wrapper around [Plexer.make] to take an offset into account. *)

let offset = ref 0

let with_offset n f x =
  let old = !offset in
  try
    offset := n; let y = f x in offset := old; y
  with e ->
    offset := old; raise e

let loc_offset lf n = 
  IFDEF OCAML307 THEN
  let (b,e) = lf n in (b + !offset, e + !offset)
  ELSE
  let (b,e) = lf n in 
    ({ b with Lexing.pos_cnum = b.Lexing.pos_cnum + !offset }, 
     { e with Lexing.pos_cnum = b.Lexing.pos_cnum + !offset })
  END

let lexer = 
  let l = Plexer.make () in
  { l with 
    Token.func = fun cs -> let ts,lf = l.Token.func cs in ts, loc_offset lf }

let join (b,_) (_,e) = (b,e)

(*s grammar entries *)

let gram = Grammar.create lexer
let gec s = Grammar.Entry.create gram s

(* logic *)
let lexpr = gec "lexpr"
let lexpr00 = gec "lexpr00"
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
let type_var = gec "type_var"
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
let exn_condition = gec "exn_condition"

(* binders *)
let binder  = gec "binder"
let binder_type = gec "binder_type"
let binders  = gec "binders"
let logic_binder = gec "logic_binder"

(* programs *)
let program = gec "program"
let prog1 = gec "prog1"
let prog2 = gec "prog2"
let prog3 = gec "prog3"
let prog4 = gec "prog4"
let plus_minus = gec "plus_minus"
let times_div_mod = gec "times_div_mod"
let prog5 = gec "prog5"
let prog6 = gec "prog6"
let prog7 = gec "prog7"
let recfun = gec "recfun"
let arg = gec "arg"
let block = gec "block"
let any_block = gec "any_block"
let block_statement = gec "block_statement"
let handler = gec "handler"
let relation = gec "relation"
let ident = gec "ident"
let ident_or_string = gec "ident_or_string"
let qualid_ident = gec "qualid_ident"
let invariant = gec "invariant"
let variant = gec "variant"
let exception_type = gec "exception_type"
let assertion = gec "assertion"
let lexpr = gec "lexpr"
let name = gec "name"

let decl = gec "decl"
let decls = gec "decls"
let external_ = gec "external_"
let logic_type = gec "logic_type"
let logic_arg = gec "logic_arg"

(*s Utility functions. *)

let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
let mk_pp loc = mk_ppl (make_loc loc)

let infix_ppl loc a i b = mk_ppl loc (PPinfix (a, i, b))
let infix_pp loc = infix_ppl (make_loc loc)

let prefix_ppl loc p a = mk_ppl loc (PPprefix (p, a))
let prefix_pp loc = prefix_ppl (make_loc loc)

let conj_assert {a_name=n; a_value=a} {a_value=b} = 
  let loc = join a.pp_loc b.pp_loc in
  { a_value = infix_ppl loc a PPand b; a_name = n; a_loc = loc }

let conj = function
  | None, None     -> None
  | None, b        -> b
  | a, None        -> a
  | Some (a,[]), Some (b,[]) -> Some (conj_assert a b, [])
  | _ -> assert false (* TODO *)

let without_annotl loc d = 
  { pdesc = d; pre = []; oblig = []; post = None; ploc = loc }

let without_annot loc = without_annotl (make_loc loc)

let no_loc (_,e) = (e,e)

let rec app f = function
  | [] -> 
      assert false
  | [a] -> 
      Sapp (f, a)
  | a :: l -> 
      let loc = join f.ploc (arg_loc a) in 
      app (without_annotl loc (Sapp (f, a))) l

let bin_op (loc_op,op) loc e1 e2 =
  let loc_op = make_loc loc_op in
  let f = without_annotl loc_op (Svar op) in
  let f_e1 = without_annotl (join e1.ploc loc_op) (Sapp (f, Sterm e1)) in
  without_annot loc (Sapp (f_e1, Sterm e2))

let un_op op loc e =
  without_annot loc
    (app (without_annot loc (Svar op)) [Sterm e])

let mk_prog loc p pre post =
  { pdesc = p.pdesc; 
    pre = pre; 
    oblig = p.pre @ p.oblig;
    post = conj (p.post, post); 
    ploc = make_loc loc }

let rec_name = function Srec (x,_,_,_,_) -> x | _ -> assert false

let check_block loc b =
  let is_statement = function Sstatement _ -> true | _ -> false in
  if not (List.exists is_statement b) then
    Report.raise_located (make_loc loc)
      (Error.AnyMessage "a sequence must contain at least one statement")

EXTEND 

  ident:
  [ [ id = LIDENT -> Ident.create id
    | id = UIDENT -> Ident.create id ] ]
  ;
  ident_or_string:
  [ [ id = ident -> Ident.string id
    | s = STRING -> s ] ]
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
    | f = FLOAT -> let (f,i,e) = Float_lexer.split f in ConstFloat (f,i,e) ] ]
  ;
  lexpr:
  [ [ ":"; id = ident_or_string; ":"; a = lexpr -> 
	mk_pp loc (PPnamed (id, a))
    | a = lexpr00 -> a ] ]
  ;
  lexpr00:  
  [ [ a = lexpr0; "->"; b = lexpr00 -> infix_pp loc a PPimplies b
    | a = lexpr0; "<->"; b = lexpr00 -> infix_pp loc a PPiff b
    | a = lexpr0 -> a ] ]
  ; 
  lexpr0:
  [ [ a = lexpr1; "or"; b = lexpr0 -> infix_pp loc a PPor b
    | a = lexpr1 -> a ] ]
  ; 
  lexpr1:
  [ [ a = lexpr2; "and"; b = lexpr1 -> infix_pp loc a PPand b
    | a = lexpr2 -> a ] ]
  ;
  lexpr2:
  [ [ LIDENT "not"; a = lexpr3 -> prefix_pp loc PPnot a
    | a = lexpr3 -> a ] ]  ;
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
    | LIDENT "forall"; id = ident; ":"; t = logic_arg; "." ; a = lexpr -> 
	mk_pp loc (PPforall (id, t, a))
    | LIDENT "exists"; id = ident; ":"; t = logic_arg; "." ; a = lexpr -> 
	mk_pp loc (PPexists (id, t, a))
    | LIDENT "fpi"; "("; e = lexpr; ","; f1 = FLOAT; ","; f2 = FLOAT; ")" ->
	let f1 = Float_lexer.split f1 in
	let f2 = Float_lexer.split f2 in
	mk_pp loc (PPfpi (e, f1, f2))
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
  type_var:
  [ [ "'" ; v = ident -> v ] ]
  ;
  primitive_type:
  [ [ "int" -> PTint
    | "bool" -> PTbool
    | "real" -> PTreal
    | "unit" -> PTunit 
    | v = type_var -> PTvarid v
    | id = ident -> PTexternal ([],id) 
    | t = primitive_type ; id = ident -> PTexternal ([t],id) 
    | "("; l = LIST1 primitive_type SEP ","; ")" ; id = ident -> 
	PTexternal (l,id) 
    ] ] 
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
  [ [ v = simple_type_v; "array" -> PVarray v
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
  [ [ "reads"; l = LIST0 ident SEP "," -> l ] ]
  ;
  writes:
  [ [ "writes"; l = LIST0 ident SEP "," -> l ] ]
  ;
  raises:
  [ [ "raises"; l = LIST0 ident SEP "," -> l ] ]
  ;
  pre_condition:
  [ [ c = assertion -> c ] ]
  ;
  post_condition:
  [ [ c = assertion -> (c,[]) 
    | c = assertion; "|"; l = LIST1 exn_condition SEP "|" -> (c,l) 
    | "|"; l = LIST1 exn_condition SEP "|" -> 
	wprintf (make_loc loc) "no postcondition; false inserted@\n";
        if werror then exit 1;
	(anonymous (make_loc loc) (mk_pp loc PPfalse), l)
  ] ]
  ;
  exn_condition:
  [ [ x = ident; "=>"; c = assertion -> (x,c) ] ]
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
  [ [ c = lexpr; n = name -> 
       { a_name = n; a_value = c; a_loc = make_loc loc } ] ]
  ;
  name:
  [ [ "as"; id = ident -> Ident.Name id
    | -> Ident.Anonymous ] ]
  ;

  program:
  [ [ p = prog1 -> p ] ]
  ;
  prog1:
  [ [ x = prog2; "||"; y = prog1  -> 
       let ptrue = without_annot (no_loc loc) (Sconst (ConstBool true)) in
       without_annot loc (Sif (x, ptrue, y))
    | x = prog2; "&&"; y = prog1 -> 
       let pf = without_annot (no_loc loc) (Sconst (ConstBool false)) in
       without_annot loc (Sif (x, y, pf))
    | x = prog2 -> x ] ]
  ;
  prog2:
  [ [ LIDENT "not"; x = prog3 -> 
       let pf = without_annot (no_loc loc) (Sconst (ConstBool false)) in
       let pt = without_annot (no_loc loc) (Sconst (ConstBool true)) in
       without_annot loc (Sif (x, pf, pt))
    | x = prog3 -> x ] ]
  ;
  prog3:
  [ [ x = prog4; rel = relation; y = prog4 -> bin_op rel loc x y
    | x = prog4 -> x ] ]
  ;
  prog4:
  [ [ x = prog5; op = plus_minus; y = prog4 -> bin_op op loc x y
    | x = prog5 -> x ] ]
  ;
  plus_minus:
  [ [ "+" -> loc, Ident.t_add
    | "-" -> loc, Ident.t_sub ] ]
  ;
  prog5:
  [ [ x = prog6; op = times_div_mod; y = prog5 -> bin_op op loc x y 
    | x = prog6 -> x ] ]
  ;
  times_div_mod:
  [ [ "*" -> loc, Ident.t_mul
    | "/" -> loc, Ident.t_div
    | "%" -> loc, Ident.t_mod_int ] ]
  ;
  prog6:
  [ [ "-"; x = prog6 -> un_op Ident.t_neg loc x
    | LIDENT "sqrt_real"; x = prog6 -> un_op Ident.t_sqrt_real loc x
    | x = prog7 -> x ] ]
  ;
  prog7:
  [ [ v = ident -> 
	without_annot loc (Svar v)
    | n = INT ->
	without_annot loc (Sconst (ConstInt (int_of_string n)))
    | f = FLOAT ->
	let f = Float_lexer.split f in
	without_annot loc (Sconst (ConstFloat f))
    | LIDENT "void" ->
	without_annot loc (Sconst ConstUnit)
    | "true" ->
	without_annot loc (Sconst (ConstBool true))
    | "false" ->
	without_annot loc (Sconst (ConstBool false))
    | "!"; v = ident ->
	without_annot loc (Srefget v)
    | v = ident; ":="; p = program ->
	without_annot loc (Srefset (v,p))
    | v = ident; "["; e = program; "]" -> 
	without_annot loc (Sarrget (true,v,e))
    | v = ident; "["; e = program; "]"; ":="; p = program -> 
	without_annot loc (Sarrset (true,v,e,p))
    | "if"; e1 = program; "then"; e2 = program; "else"; e3 = program ->
	without_annot loc (Sif (e1,e2,e3))
    | "if"; e1 = program; "then"; e2 = program ->
	without_annot loc (Sif (e1, e2,
				without_annot (no_loc loc) (Sconst ConstUnit)))
    | "while"; b = program; "do"; 
	"{"; inv = OPT invariant; LIDENT "variant"; wf = variant; "}";
	(bl_loc,bl) = block; "done" ->
	without_annot loc (Swhile (b, inv, wf, without_annot bl_loc (Sseq bl)))
(*i
    | "for"; i = ident; "="; v1 = program; "to"; v2 = program;
	"do"; "{"; inv = invariant; "}"; bl = block; "done" -> 
	  make_ast_for loc i v1 v2 inv bl
i*)
    | "let"; v = ident; "="; "ref"; p1 = program; "in"; p2 = program ->
	without_annot loc (Sletref (v, p1, p2))
    | "let"; v = ident; "="; p1 = program; "in"; p2 = program ->
	without_annot loc (Sletin (v, p1, p2))
    | "begin"; (_,b) = block; "end" ->
	without_annot loc (Sseq b)
    | "fun"; bl = binders; "->"; p = program ->
	without_annot loc (Slam (bl,p))
    | "let"; "rec"; p = recfun -> 
        without_annot loc p
    | "let"; "rec"; p = recfun; "in"; p2 = program ->
	without_annot loc (Sletin (rec_name p, without_annot loc p, p2))
    | "raise"; id = ident; t = OPT cast ->
	without_annot loc (Sraise (id, None, t))
    | "raise"; "("; id = ident; p = program; ")"; t = OPT cast ->
	without_annot loc (Sraise (id, Some p, t))
    | "try"; p = program; "with"; hl = LIST1 handler SEP "|"; "end" ->
	without_annot loc (Stry (p, hl))
    | "absurd"; t = OPT cast ->
	without_annot loc (Sabsurd t)
    | "["; c = type_c; "]" ->
	without_annot loc (Sany c)
    | "("; p = program; args = LIST0 arg; ")" ->
	if args = [] then p else without_annot loc (app p args)
    | "{"; pre = OPT pre_condition; "}"; p = program; 
      "{"; post = OPT post_condition; "}" -> 
        mk_prog loc p (list_of_some pre) post
    | l = ident; ":"; p = program ->
	without_annot loc (Sseq [Slabel (Ident.string l); Sstatement p])
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
  [ [ b = any_block -> check_block loc b; loc, b ] ]
  ;
  any_block:
  [ [ s = block_statement; ";"; b = any_block -> s :: b
    | s = block_statement                 -> [s] ] ]
  ;
  block_statement:
  [ [ LIDENT "label"; s = ident -> Slabel (Ident.string s)
    | LIDENT "assert"; "{"; c = assertion; "}" -> Sassert c 
    | p = program -> Sstatement p ] ]
  ;
  handler:
  [ [ x = ident; "->"; p = program -> ((x, None), p)
    | x = ident; v = ident; "->"; p = program -> ((x, Some v), p)
  ] ]
  ;
  relation:
    [ [ "<"  -> loc, Ident.t_lt
      | "<=" -> loc, Ident.t_le
      | ">"  -> loc, Ident.t_gt
      | ">=" -> loc, Ident.t_ge
      | "="  -> loc, Ident.t_eq
      | "<>" -> loc, Ident.t_neq ] ] 
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
    | e = external_; 
      "parameter"; ids = LIST1 ident SEP ","; ":"; v = type_v -> 
	Parameter (make_loc loc, e, ids, v)
    | "exception"; id = ident; v = OPT exception_type ->
	Exception (make_loc loc, id, v)
    | e = external_; "logic"; ids = LIST1 ident SEP ","; ":"; t = logic_type ->
	Logic (make_loc loc, e, ids, t)
    | "axiom"; id = ident; ":"; p = lexpr ->
	Axiom (make_loc loc, id, p)
    | "predicate"; id = ident; "("; bl = LIST0 logic_binder SEP ","; ")";
      "="; p = lexpr ->
	Predicate_def (make_loc loc, id, bl, p)
    | "function"; id = ident; "("; bl = LIST0 logic_binder SEP ","; ")"; ":";
        t = primitive_type; "="; p = lexpr ->
	Function_def (make_loc loc, id, bl, t, p)
    | "goal"; id = ident; ":"; p = lexpr ->
	Assert (make_loc loc, id, p)
  ] ]
  ;
  logic_binder:
  [ [ id = ident; ":"; t = primitive_type -> (id, t) ] ]
  ;
  external_:
  [ [ "external" -> true | -> false ] ]
  ;
  decls: 
  [ [ d = LIST0 decl; EOI -> d ] ]
  ;
  logic_type:
  [ [ b = LIST0 logic_arg SEP ","; "->"; LIDENT "prop" -> Predicate b
    | b = LIST0 logic_arg SEP ","; "->"; t = primitive_type -> Function (b, t)
  ] ]
  ;
  logic_arg:
  [ [ t = primitive_type -> t
    | t = primitive_type; "array" -> PTarray t
  ] ]
  ;

END
;;

