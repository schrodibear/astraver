/*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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
 */

/* from http://www.lysator.liu.se/c/ANSI-C-grammar-y.html */

%{

  open Format
  open Coptions
  open Clogic
  open Ptree
  open Cast
  open Parsing

  let loc () = (symbol_start (), symbol_end ())
  let loc_i i = (rhs_start i, rhs_end i)

  let locate x = { node = x; loc = loc() }
  let locate_i i x = { node = x; loc = loc_i i }
  let with_loc l x = { node = x; loc = l }

  let info x = { Clogic.node = x; info = loc () }

  let error s = raise (Stdpp.Exc_located (loc (), Stream.Error s))

  let uns () =
    raise (Stdpp.Exc_located (loc (), Stream.Error "Unsupported C syntax"))
  let unss s =
    raise (Stdpp.Exc_located (loc (), 
			      Stream.Error ("Unsupported C syntax: " ^ s)))
  let warning s =
    Format.eprintf "%a warning: %s\n" Loc.report_line (symbol_start ()) s
  let vwarning s = if verbose then warning s
  let dwarning s = if debug then warning s

  let add_pre_loc lb = function
    | Some (b,_) -> Loc.join (b,0) lb 
    | _ -> lb

  let expr_of_statement s = match s.node with
    | CSnop -> { node = CEnop; loc = s.loc }
    | CSexpr e -> e
    | _ -> assert false

  (* used only for parsing types *)

  type specifier = 
    | Stypedef 
    | Sstorage of storage_class
    | Stype of cexpr ctype_node
    | Slong
    | Sshort
    | Sconst
    | Svolatile
    | Srestrict
    | Ssign of sign
    | Sstruct_decl of string option * fields
    | Sunion_decl of string option * fields
	
  and specifiers = specifier list

  and declarator =
    | Dsimple
    | Dpointer of declarator
    | Darray of declarator * cexpr option
    | Dfunction of declarator * parameters * annot option

  and parameters = (specifiers * declarator * string) list

  and fields = (specifiers * declarator * string * cexpr option) list

  (* interps a list of specifiers / declarators as a [ctype] *)
  (* TODO: short/long *)

  let storage_class = 
    let rec loop st = function
      | [] -> 
	  st
      | Sstorage st' :: s when st = No_storage -> 
	  loop st' s
      | Sstorage st' :: s when st' = st ->
	  warning "duplicate storage class"; loop st s
      | Sstorage st' :: _ ->
	  error "multiple storage class"
      | _ :: s -> 
	  loop st s
    in
    loop No_storage

  let sign =
    let rec loop so = function
      | [] -> 
	  so
      | Ssign b' :: sp -> 
	  (match so with 
	     | None -> loop (Some b') sp
	     | Some b when b = b' -> warning "duplicate (un)signed"; loop so sp
	     | Some b -> error "both signed and unsigned")
      | _ :: sp -> 
	  loop so sp
    in
    loop None

  let apply_sign sg ty = match sg, ty with
    | None, t -> t
    | Some b, (CTint (_, i)) -> CTint (b, i)
    | Some _, _ -> error "signed or unsigned invalid"

  type length = Short | Long | LongLong

  let length =
    let rec loop lo = function
      | [] -> 
	  lo
      | (Sshort | Slong as s) :: sp -> 
	  (match s, lo with 
	     | Sshort, None -> 
		 loop (Some Short) sp
	     | Slong, None -> 
		 loop (Some Long) sp
	     | Sshort, Some Short -> 
		 warning "duplicate short"; loop lo sp
	     | Sshort, Some (Long | LongLong) | Slong, Some Short -> 
		 error "both long and short specified"
	     | Slong, Some Long -> 
		 loop (Some LongLong) sp
	     | Slong, Some LongLong ->
		 error "too long for caduceus"
	     | _ -> 
		 assert false)
      | _ :: sp -> 
	  loop lo sp
    in
    loop None

  (* debug *)
  let rec explain_type fmt = function
    | CTfun (_, t) -> 
	fprintf fmt "function returning %a" explain_type t.ctype_node
    | CTpointer t -> 
	fprintf fmt "pointer on %a" explain_type t.ctype_node
    | CTarray (t, _) -> 
	fprintf fmt "array[] of %a" explain_type t.ctype_node
    | _ -> 
	fprintf fmt "other"

  (* fresh names for anonymous structures *)

  let fresh_name =
    let r = ref (-1) in
    function 
      | Some s -> s
      | None -> incr r; "%_anonymous_" ^ string_of_int !r

  (* Interpretation of type expression.
     [gl] indicates a global declaration (implies the check for a type or 
     a storage class) *)

  let rec interp_type gl specs decl = 
    let st = storage_class specs in
    let cst = List.exists ((=) Sconst) specs in
    let vl = List.exists ((=) Svolatile) specs in
    let sg = sign specs in
    let lg = length specs in
    let noattr n = { ctype_node = n; ctype_storage = No_storage;
		     ctype_const = false; ctype_volatile = false } in
    let rec base_type tyo = function
      | [] -> 
	  (match tyo with 
	     | Some ty -> ty 
	     | None when gl && st = No_storage && sg = None && lg = None -> 
		 error "data definition has no type or storage class"
	     | None -> CTint (Signed, Int))
      | Stype t :: sp when tyo = None ->
	  base_type (Some t) sp
      | Sstruct_decl (so, pl) :: sp when tyo = None ->
	  base_type (Some (CTstruct (fresh_name so, fields pl))) sp
      | Sunion_decl (so, pl) :: sp when tyo = None ->
	  base_type (Some (CTunion (fresh_name so, fields pl))) sp
      | (Stype _ | Sstruct_decl _ | Sunion_decl _) :: _ ->
	  error "two or more data types in declaration"
      | _ :: sp ->
	  base_type tyo sp
    and full_type ty = function
      | Dsimple -> ty
      | Dpointer d -> full_type (noattr (CTpointer ty)) d
      | Darray (d, so) -> full_type (noattr (CTarray (ty, so))) d
      | Dfunction (d, pl, _) -> full_type (noattr (CTfun (params pl, ty))) d
    and params pl = 
      List.map (fun (s,d,x) -> (interp_type false s d, x)) pl
    and fields fl =
      List.map (fun (s,d,x,bf) -> (interp_type false s d, x, bf)) fl
    in
    let bt = base_type None specs in
    let bt = apply_sign sg bt in
    let bt = { ctype_node = bt; ctype_storage = st;
	       ctype_const = cst; ctype_volatile = vl } 
    in
    let ty = full_type bt decl in
    if debug then eprintf "%a@." explain_type ty.ctype_node;
    ty

  let interp_param (s, d, id) = interp_type false s d, id
  let interp_params = List.map interp_param

  let is_typedef = List.exists ((=) Stypedef)

  let declaration specs decls =
    let l = loc() in
    if is_typedef specs then
      let interp = function
	| (n,d), Inothing -> 
	    Ctypes.add n; Ctypedef (interp_type true specs d, n)
	| (n,_), _ -> 
	    error ("typedef " ^ n ^ " is initialized")
      in
      List.map interp decls
    else
      let interp ((n,d),i) =
	Ctypes.remove n; Cdecl (interp_type true specs d, n, i)
      in
      List.map interp decls

  let type_declarations specs =
    if is_typedef specs then warning "useless keyword in empty declaration";
    let ty = interp_type true specs Dsimple in
    match ty.ctype_node with
      | CTstruct _ | CTunion _ | CTenum _ 
      | CTstruct_named _ | CTunion_named _ | CTenum_named _ ->
          [ locate (Ctypedecl ty) ]
      | _ ->
	  warning "empty declaration";
	  []

  (* old style function prototype: f(x,y,z) t1 x; t2 y; ...
     some parameters may be omitted *)
  let old_style_params pl decls =
    let pids = List.map (fun (_,_,x) -> x) pl in
    let h = Hashtbl.create 17 in
    (* we first check that no parameter is initialized or occurs twice *)
    List.iter
      (fun d -> match d.node with
	 | Cdecl (ty, x, Inothing) -> 
	     if not (List.mem x pids) then 
	       error ("declaration for " ^ x ^ " but no such parameter");
	     if Hashtbl.mem h x then error ("duplicate declaration for " ^ x);
	     Hashtbl.add h x ty
	 | Cdecl (_,x,_) -> error ("parameter " ^ x ^ " is initialized")
	 | _ -> ()) decls;
    (* look for the type for [x] in decls; defaults to [int] *)
    let type_for x =
      try Hashtbl.find h x with Not_found -> interp_type false [] Dsimple
    in
    (* do it for all parameters *)
    List.map
      (function 
	 | ([], Dsimple, x) -> 
	     (type_for x, x)
	 | _ -> 
	     error "parm types given both in parmlist and separately")
      pl

  let function_declaration specs d decls = match d with
    | id, Dfunction (d, pl, p) ->
	let ty = interp_type false specs d in
	let pl = 
	  if decls = [] then interp_params pl else old_style_params pl decls 
	in
	List.iter (fun (_,x) -> Ctypes.remove x) pl;
	ty, id, pl, p
    | _ -> 
	raise Parsing.Parse_error

%}

%token <int * string> ANNOT
%token <int * string> WDECL

%token <string> IDENTIFIER CONSTANT STRING_LITERAL TYPE_NAME
%token SIZEOF
%token PTR_OP INC_OP DEC_OP LEFT_OP RIGHT_OP LE_OP GE_OP EQ_OP NE_OP
%token AND_OP OR_OP MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN
%token SUB_ASSIGN LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN
%token XOR_ASSIGN OR_ASSIGN

%token TYPEDEF EXTERN STATIC AUTO REGISTER
%token CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE CONST VOLATILE VOID
%token STRUCT UNION ENUM ELLIPSIS

%token CASE DEFAULT IF ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN

%token SEMICOLON LBRACE RBRACE COMMA COLON EQUAL LPAR RPAR LSQUARE RSQUARE
%token DOT AMP EXL TILDE MINUS PLUS STAR SLASH PERCENT LT GT HAT PIPE
%token QUESTION EOF

/* non-ANSI tokens */
%token ATTRIBUTE RESTRICT

/* extra tokens for the logic */
%token FORALL EXISTS AND OR NOT TRUE FALSE OLD RESULT LENGTH THEN AT

%nonassoc specs
%nonassoc TYPE_NAME
%nonassoc no_annot
%nonassoc ANNOT

%type <Cast.file> file
%start file
%type <Loc.t Clogic.predicate> predicate
%start predicate
%%

file
        : translation_unit EOF { $1 }
        | EOF { [] }
        ;

primary_expression
        : IDENTIFIER { locate (CEvar $1) }
        | CONSTANT { locate (CEconstant $1) }
        | STRING_LITERAL { locate (CEstring_literal $1) }
        | LPAR expression RPAR { $2 }
        ;

postfix_expression
        : primary_expression 
            { $1 }
        | postfix_expression LSQUARE expression RSQUARE 
	    { locate (CEarrget ($1, $3)) }
        | postfix_expression LPAR RPAR 
	    { locate (CEcall ($1, [])) }
        | postfix_expression LPAR argument_expression_list RPAR 
	    { locate (CEcall ($1, $3)) }
        | postfix_expression DOT identifier/*ICI*/ 
	    { locate (CEdot ($1, $3)) }
        | postfix_expression PTR_OP identifier/*ICI*/ 
	    { locate (CEarrow ($1, $3)) }
        | postfix_expression INC_OP 
	    { locate (CEunary (Upostfix_inc, $1)) }
        | postfix_expression DEC_OP
	    { locate (CEunary (Upostfix_dec, $1)) }
        ;

argument_expression_list
        : assignment_expression { [$1] }
        | argument_expression_list COMMA assignment_expression { $1 @ [$3] }
        ;

unary_expression
        : postfix_expression { $1 }
        | INC_OP unary_expression { locate (CEunary (Uprefix_inc, $2)) }
        | DEC_OP unary_expression { locate (CEunary (Uprefix_dec, $2)) }
        | unary_operator cast_expression { locate (CEunary ($1, $2)) }
        | SIZEOF unary_expression { locate (CEsizeof_expr $2) }
        | SIZEOF LPAR type_name RPAR 
	    { let s,d = $3 in locate (CEsizeof (interp_type false s d)) }
        ;

unary_operator
        : AMP { Uamp }
        | STAR { Ustar }
        | PLUS { Uplus }
        | MINUS { Uminus }
        | TILDE { Utilde }
        | EXL { Unot }
        ;

cast_expression
        : unary_expression { $1 }
        | LPAR type_name RPAR cast_expression 
	    { let s,d = $2 in locate (CEcast (interp_type false s d, $4)) }
        ;

multiplicative_expression
        : cast_expression 
            { $1 }
        | multiplicative_expression STAR cast_expression 
	    { locate (CEbinary ($1, Bmul, $3)) }
        | multiplicative_expression SLASH cast_expression 
	    { locate (CEbinary ($1, Bdiv, $3)) }
        | multiplicative_expression PERCENT cast_expression 
	    { locate (CEbinary ($1, Bmod, $3)) }
        ;

additive_expression
        : multiplicative_expression 
           { $1 }
        | additive_expression PLUS multiplicative_expression 
	    { locate (CEbinary ($1, Badd, $3)) }
        | additive_expression MINUS multiplicative_expression 
	    { locate (CEbinary ($1, Bsub, $3)) }
        ;

shift_expression
        : additive_expression { $1 }
        | shift_expression LEFT_OP additive_expression 
	    { locate (CEbinary ($1, Bshift_left, $3)) }
        | shift_expression RIGHT_OP additive_expression 
	    { locate (CEbinary ($1, Bshift_right, $3)) }
        ;

relational_expression
        : shift_expression 
            { $1 }
        | relational_expression LT shift_expression 
	    { locate (CEbinary ($1, Blt, $3)) }
        | relational_expression GT shift_expression
	    { locate (CEbinary ($1, Bgt, $3)) }
        | relational_expression LE_OP shift_expression
	    { locate (CEbinary ($1, Ble, $3)) }
        | relational_expression GE_OP shift_expression
	    { locate (CEbinary ($1, Bge, $3)) }
        ;

equality_expression
        : relational_expression 
            { $1 }
        | equality_expression EQ_OP relational_expression 
	    { locate (CEbinary ($1, Beq, $3)) }
        | equality_expression NE_OP relational_expression 
	    { locate (CEbinary ($1, Bneq, $3)) }
        ;

and_expression
        : equality_expression 
            { $1 }
        | and_expression AMP equality_expression 
	    { locate (CEbinary ($1, Bbw_and, $3)) }
        ;

exclusive_or_expression
        : and_expression 
            { $1 }
        | exclusive_or_expression HAT and_expression 
	    { locate (CEbinary ($1, Bbw_xor, $3)) }
        ;

inclusive_or_expression
        : exclusive_or_expression 
            { $1 }
        | inclusive_or_expression PIPE exclusive_or_expression 
	    { locate (CEbinary ($1, Bbw_or, $3)) }
        ;

logical_and_expression
        : inclusive_or_expression 
            { $1 }
        | logical_and_expression AND_OP inclusive_or_expression 
	    { locate (CEbinary ($1, Band, $3)) }
        ;

logical_or_expression
        : logical_and_expression 
            { $1 }
        | logical_or_expression OR_OP logical_and_expression 
	    { locate (CEbinary ($1, Bor, $3)) }
        ;

conditional_expression
        : logical_or_expression 
            { $1 }
        | logical_or_expression QUESTION expression COLON conditional_expression 
	    { locate (CEcond ($1, $3, $5)) }
        ;

assignment_expression
        : conditional_expression 
            { $1 }
        | unary_expression assignment_operator assignment_expression 
	    { locate (CEassign ($1, $2, $3)) }
        ;

assignment_operator
        : EQUAL { Aequal }
        | MUL_ASSIGN { Amul }
        | DIV_ASSIGN { Adiv }
        | MOD_ASSIGN { Amod }
        | ADD_ASSIGN { Aadd }
        | SUB_ASSIGN { Asub }
        | LEFT_ASSIGN { Aleft }
        | RIGHT_ASSIGN { Aright }
        | AND_ASSIGN { Aand }
        | XOR_ASSIGN { Axor }
        | OR_ASSIGN { Aor }
        ;

expression
        : assignment_expression { $1 }
        | expression COMMA assignment_expression { locate (CEseq ($1, $3)) }
        ;

constant_expression
        : conditional_expression { $1 }
        ;

declaration
        : declaration_specifiers SEMICOLON 
            { type_declarations $1 }
        | declaration_specifiers init_declarator_list attributes_opt SEMICOLON 
	    { List.map locate (declaration $1 $2) }
	| WDECL  /* ADDED FOR WHY */
	    { [locate (Cspecdecl $1)] }
        ;

/* the precedence specs indicates to keep going with declaration_specifiers */
declaration_specifiers
        : storage_class_specifier %prec specs { [$1] }
        | storage_class_specifier declaration_specifiers { $1 :: $2 }
        | type_specifier { [$1] }
        | type_specifier declaration_specifiers_no_name { $1 :: $2 }
        | type_qualifier %prec specs { [$1] }
        | type_qualifier declaration_specifiers { $1 :: $2 }
        ;
/* same thing, with TYPE_NAME no more allowed */
declaration_specifiers_no_name
        : storage_class_specifier %prec specs { [$1] }
        | storage_class_specifier declaration_specifiers_no_name { $1 :: $2 }
        | type_specifier_no_name { [$1] }
        | type_specifier_no_name declaration_specifiers_no_name { $1 :: $2 }
        | type_qualifier %prec specs { [$1] }
        | type_qualifier declaration_specifiers { $1 :: $2 }
        ;

init_declarator_list
        : init_declarator { [$1] }
        | init_declarator_list COMMA init_declarator { $1 @ [$3] }
        ;

init_declarator
        : declarator 
            { $1, Inothing }
        | declarator EQUAL c_initializer 
	    { $1, $3 }
        ;

storage_class_specifier
        : TYPEDEF { Stypedef }
        | EXTERN { Sstorage Extern }
        | STATIC { Sstorage Static }
        | AUTO { Sstorage Auto }
        | REGISTER { Sstorage Register }
        ;

type_specifier
        : type_specifier_no_name { $1 }
        | TYPE_NAME { Stype (CTvar $1) }
        ;
type_specifier_no_name
        : VOID { Stype CTvoid }
        | CHAR { Stype (CTint (Unsigned, Char)) }
        | SHORT { Sshort }
        | INT { Stype (CTint (Signed, Int)) }
        | LONG { Slong }
        | FLOAT { Stype (CTfloat Float) }
        | DOUBLE { Stype (CTfloat Double) }
        | SIGNED { Ssign Signed }
        | UNSIGNED { Ssign Unsigned }
        | struct_or_union_specifier { $1 }
        | enum_specifier { $1 }
        ;

identifier
        : IDENTIFIER { $1 }
        | TYPE_NAME  { $1 }
	;

struct_or_union_specifier
        : struct_or_union identifier/*ICI*/ LBRACE struct_declaration_list RBRACE 
            { if $1 then 
		Sstruct_decl (Some $2, $4) 
	      else 
		Sunion_decl (Some $2, $4) }
        | struct_or_union LBRACE struct_declaration_list RBRACE 
	    { if $1 then Sstruct_decl (None, $3) else Sunion_decl (None, $3) }
        | struct_or_union identifier/*ICI*/ 
	    { Stype (if $1 then CTstruct_named $2 else CTunion_named $2) }
        ;

struct_or_union
        : STRUCT { true }
        | UNION { false }
        ;

struct_declaration_list
        : struct_declaration { $1 }
        | struct_declaration_list struct_declaration { $1 @ $2 }
        ;

struct_declaration
        : specifier_qualifier_list struct_declarator_list SEMICOLON 
            { let s = $1 in List.map (fun ((id,d),bf) -> s,d,id,bf) $2 }
        ;

specifier_qualifier_list
        : type_specifier specifier_qualifier_list_no_name { $1 :: $2 }
        | type_specifier { [$1] }
        | type_qualifier specifier_qualifier_list { $1 :: $2 }
        | type_qualifier %prec specs { [$1] }
        ;
/* same thing, with TYPE_NAME no more allowed */
specifier_qualifier_list_no_name
        : type_specifier_no_name specifier_qualifier_list_no_name { $1 :: $2 }
        | type_specifier_no_name { [$1] }
        | type_qualifier specifier_qualifier_list_no_name { $1 :: $2 }
        | type_qualifier { [$1] }
        ;

struct_declarator_list
        : struct_declarator { [$1] }
        | struct_declarator_list COMMA struct_declarator { $1 @ [$3] }
        ;

struct_declarator
        : declarator 
            { $1, None }
        | COLON constant_expression 
	    { ("_", Dsimple), Some $2 }
        | declarator COLON constant_expression 
	    { $1, Some $3 }
        ;

enum_specifier
        : ENUM LBRACE enumerator_list RBRACE 
            { Stype (CTenum (fresh_name None, $3)) }
        | ENUM identifier/*ICI*/ LBRACE enumerator_list RBRACE 
	    { Stype (CTenum ($2, $4)) }
        | ENUM identifier/*ICI*/ 
	    { Stype (CTenum_named $2) }
        ;

enumerator_list
        : enumerator { [$1] }
        | enumerator_list COMMA enumerator { $1 @ [$3] }
        ;

enumerator
        : IDENTIFIER { $1, None }
        | IDENTIFIER EQUAL constant_expression { $1, Some $3 }
        ;

type_qualifier
        : CONST { Sconst }
        | VOLATILE { Svolatile }
	| RESTRICT { dwarning "ignored __restrict"; Srestrict }
        ;

declarator
        : pointer direct_declarator { let id,d = $2 in id, $1 d }
        | direct_declarator { $1 }
        ;

direct_declarator
        : identifier
            { $1, Dsimple }
        | LPAR declarator RPAR 
	    { $2 }
        | direct_declarator LSQUARE constant_expression RSQUARE 
	    { let id,d = $1 in id, Darray (d, Some $3) }
        | direct_declarator LSQUARE RSQUARE 
	    { let id,d = $1 in id, Darray (d, None) }
        | direct_declarator LPAR parameter_type_list RPAR annot 
	    { let id,d = $1 in id, Dfunction (d, $3, $5) }
        | direct_declarator LPAR identifier_list RPAR annot
	    { let pl = List.map (fun x -> ([], Dsimple, x)) $3 in
	      let id,d = $1 in id, Dfunction (d, pl, $5) }
        | direct_declarator LPAR RPAR annot 
            { let id,d = $1 in id, Dfunction (d, [], $4) }
        ;

/* ADDED FOR WHY */
annot
        : ANNOT         { Some $1 }
        | /* epsilon */ %prec no_annot { None }
        ;

pointer
        : STAR { fun d -> Dpointer d }
        | STAR type_qualifier_list 
	    { dwarning "ignored qualifiers"; fun d -> Dpointer d }
        | STAR pointer { fun d -> Dpointer ($2 d) }
        | STAR type_qualifier_list pointer 
	    { dwarning "ignored qualifiers"; fun d -> Dpointer ($3 d) }
        ;

type_qualifier_list
        : type_qualifier { [$1] }
        | type_qualifier_list type_qualifier { $1 @ [$2] }
        ;


parameter_type_list
        : parameter_list { $1 }
        /* TODO */
        | parameter_list COMMA ELLIPSIS { dwarning "ignored <...>"; $1 }
        ;

parameter_list
        : parameter_declaration { [$1] }
        | parameter_list COMMA parameter_declaration { $1 @ [$3] }
        ;

parameter_declaration
        : declaration_specifiers declarator 
            { let id,d = $2 in $1, d, id }
        | declaration_specifiers abstract_declarator 
	    { $1, $2, "_" }
        | declaration_specifiers 
	    { ($1, Dsimple, "_") }
        ;

identifier_list
        : IDENTIFIER { [$1] }
        | identifier_list COMMA IDENTIFIER { $1 @ [$3] }
        ;

type_name
        : specifier_qualifier_list { $1, Dsimple }
        | specifier_qualifier_list abstract_declarator { $1, $2 }
        ;

abstract_declarator
        : pointer { $1 Dsimple }
        | direct_abstract_declarator { $1 }
        | pointer direct_abstract_declarator { $1 $2 }
        ;

direct_abstract_declarator
        : LPAR abstract_declarator RPAR 
            { $2 }
        | LSQUARE RSQUARE 
	    { Darray (Dsimple, None) }
        | LSQUARE constant_expression RSQUARE 
	    { Darray (Dsimple, Some $2) }
        | direct_abstract_declarator LSQUARE RSQUARE 
	    { Darray ($1, None) }
        | direct_abstract_declarator LSQUARE constant_expression RSQUARE 
	    { Darray ($1, Some $3) }
        | LPAR RPAR 
	    { Dfunction (Dsimple, [], None) }
        | LPAR parameter_type_list RPAR 
	    { Dfunction (Dsimple, $2, None) }
        | direct_abstract_declarator LPAR RPAR 
	    { Dfunction ($1, [], None) }
        | direct_abstract_declarator LPAR parameter_type_list RPAR 
	    { Dfunction ($1, $3, None) }
        ;

c_initializer
        : assignment_expression { Iexpr $1 }
        | LBRACE c_initializer_list RBRACE { Ilist $2 }
        | LBRACE c_initializer_list COMMA RBRACE { Ilist $2 }
        ;

c_initializer_list
        : c_initializer { [$1] }
        | c_initializer_list COMMA c_initializer { $1 @ [$3] }
        ;

statement
        : labeled_statement { $1 }
        | compound_statement { locate (CSblock $1) }
        | expression_statement { $1 }
        | selection_statement { $1 }
        | iteration_statement { $1 }
        | jump_statement { $1 }
        ;

labeled_statement
        : identifier/*ICI*/ COLON statement { locate (CSlabel ($1, $3)) }
        | CASE constant_expression COLON statement { locate (CScase ($2, $4)) }
        | DEFAULT COLON statement { locate (CSlabel ("%default%", $3)) }
        ;

compound_statement
        : compound_statement_LBRACE RBRACE 
            { Ctypes.pop (); [], [] }
        | compound_statement_LBRACE statement_list RBRACE 
	    { Ctypes.pop (); [], $2 }
        | compound_statement_LBRACE declaration_list RBRACE 
	    { Ctypes.pop (); $2, [] }
        | compound_statement_LBRACE declaration_list statement_list RBRACE 
	    { Ctypes.pop (); $2, $3 }
        ;

compound_statement_LBRACE:
  LBRACE { Ctypes.push () }
;

/* ADDED FOR WHY */
compound_statement_with_post
        : compound_statement annot { ($1, $2) }
        ;

declaration_list
        : declaration { $1 }
        | declaration_list declaration { $1 @ $2 }
        ;

statement_list
        : statement { [$1] }
        | statement_list statement { $1 @ [$2] }
        ;

expression_statement
        : SEMICOLON { locate CSnop }
	| ANNOT SEMICOLON { locate (CSannot $1) } /* ADDED FOR WHY */
        | expression SEMICOLON { locate (CSexpr $1) }
        ;

selection_statement
        : IF LPAR expression RPAR statement 
            { locate (CSif ($3, $5, locate CSnop)) }
        | IF LPAR expression RPAR statement ELSE statement 
	    { locate (CSif ($3, $5, $7)) }
        | SWITCH LPAR expression RPAR statement 
	    { locate (CSswitch ($3, $5)) }
        ;

iteration_statement
        : WHILE LPAR expression RPAR annot statement 
            { locate (CSwhile ($3, $5, $6)) }
        | DO statement annot WHILE LPAR expression RPAR SEMICOLON 
	    { locate (CSdowhile ($2, $3, $6)) }
        | FOR LPAR expression_statement expression_statement RPAR 
          annot statement
	    { locate (CSfor (expr_of_statement $3, expr_of_statement $4, 
			     locate CEnop, $6, $7)) }
        | FOR LPAR expression_statement expression_statement expression RPAR 
          annot statement 
	    { locate (CSfor (expr_of_statement $3, expr_of_statement $4, 
			     $5, $7, $8)) }
        ;

jump_statement
        : GOTO identifier/*ICI*/ SEMICOLON { locate (CSgoto $2) }
        | CONTINUE SEMICOLON { locate CScontinue }
        | BREAK SEMICOLON { locate CSbreak }
        | RETURN SEMICOLON { locate (CSreturn None) }
        | RETURN expression SEMICOLON { locate (CSreturn (Some $2)) }
        ;

translation_unit
        : external_declaration { $1 }
        | translation_unit external_declaration { $1 @ $2 }
        ;

external_declaration
        : function_definition { [$1] }
        | declaration { $1 }
        ;

function_definition
        : function_prototype compound_statement_with_post
            { Ctypes.pop (); (* pushed by function_prototype *)
	      let ty,id,pl,p = $1 in
	      let b,q = $2 in
	      locate (Cfundef (ty, id, pl, (p,b,q))) }
        ;
	      
function_prototype
        : declaration_specifiers declarator declaration_list 
            { Ctypes.push (); function_declaration $1 $2 $3 }
        | declaration_specifiers declarator 
	    { Ctypes.push (); function_declaration $1 $2 [] }
        | declarator declaration_list
	    { Ctypes.push (); function_declaration [] $1 $2 }
        | declarator
	    { Ctypes.push (); function_declaration [] $1 [] }
        ;

/* non-ANSI */

attributes_opt:
  /* empty */ {}
| attributes { dwarning "ignored attributes" }
;

attributes:
  attribute {}
| attributes attribute {} 
;

attribute:
  ATTRIBUTE LPAR LPAR attribute_list RPAR RPAR {}
;

attribute_list:
  attrib {}
| attribute_list COMMA attrib {}
;

attrib:
  /* empty */ {}
| identifier {}
| identifier LPAR RPAR {}
| identifier LPAR argument_expression_list RPAR {}
;


/* C annotations */

predicate:
  predicate0 PTR_OP predicate { info (Pimplies ($1, $3)) }
| predicate0 { $1 }
;

predicate0:
  predicate1 OR predicate0 { info (Por ($1, $3)) }
| predicate1 { $1 }
;

predicate1:
  predicate2 AND predicate1 { info (Pand ($1, $3)) }
| predicate2 { $1 }
;

predicate2:
  NOT predicate3 { info (Pnot $2) }
| predicate3 { $1 }
;

predicate3:
  TRUE { info Ptrue }
| FALSE { info Pfalse }
| IDENTIFIER { info (Pvar $1) }
| term relation term { info (Prel ($1, $2, $3)) }
| term relation term relation term { info 
				       (Pand (info (Prel ($1, $2, $3)),
					      info (Prel ($3, $4, $5)))) }
;

relation:
  | LT { Lt } 
  | GT { Gt }
  | LE_OP { Le }
  | GE_OP { Ge }
  | EQ_OP { Eq }
  | NE_OP { Neq }
;

term:
| IDENTIFIER { info (Tvar ($1, Current)) }
| IDENTIFIER AT { info (Tvar ($1, Before)) }
| IDENTIFIER AT IDENTIFIER { info (Tvar ($1, At $3)) }
;

%%

(***
(* Entries for the C parser *)

type 'a c_parser = int -> string -> 'a

val parse_c_spec : (lexpr asst list * Effect.t * lexpr post option) c_parser
val parse_c_pre : (lexpr asst option * variant option) c_parser
val parse_c_post : (lexpr post option) c_parser
val parse_c_loop_annot : (lexpr asst option * variant) c_parser
val parse_c_decl : decl c_parser
val parse_c_annot : block_st c_parser
***)

(***

let c_pre_condition = gec "c_pre_condition"
let c_post_condition = gec "c_post_condition"
let c_spec = gec "c_spec"
let c_loop_annot = gec "c_loop_annot"
let c_pre = gec "c_pre"
let c_variant = gec "c_variant"
let c_post = gec "c_post"
let c_annot = gec "c_annot"

EXTEND
  c_pre_condition:
  [ [ LIDENT "pre"; p = pre_condition -> p ] ];
  c_post_condition:
  [ [ LIDENT "post"; q = post_condition -> q ] ];
  c_spec:
  [ [ p = OPT c_pre_condition; e = effects; q = OPT c_post_condition; EOI -> 
      (list_of_some p, e, q)
  ] ];
  c_loop_annot:
  [ [ i = OPT invariant; LIDENT "variant"; v = variant -> i,v
  ] ];
  c_pre:
  [ [ p = OPT pre_condition; v = OPT c_variant -> p,v ] ];
  c_variant:
  [ [ LIDENT "variant"; v = variant -> v ] ];
  c_post:
  [ [ q = OPT post_condition -> q ] ];
  c_annot:
  [ [ LIDENT "assert"; p = assertion -> Sassert p 
    | LIDENT "label"; s = ident -> Slabel (Ident.string s) ] ];
END
;;

type 'a c_parser = int -> string -> 'a

let parse_with_offset f n s =
  (* Options.if_debug_3 Format.eprintf "parse_with_offset : %d %s@\n" n s; *)
  let st = Stream.of_string s in
  with_offset n (Grammar.Entry.parse f) st

let parse_c_spec = parse_with_offset c_spec
let parse_c_pre = parse_with_offset c_pre
let parse_c_post = parse_with_offset c_post
let parse_c_loop_annot = parse_with_offset c_loop_annot
let parse_c_decl = parse_with_offset decl
let parse_c_annot = parse_with_offset c_annot

***)

