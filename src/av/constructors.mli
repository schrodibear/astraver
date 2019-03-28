(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Env
open Ast
open Fenv

class identifier :
  ?pos:Loc.position ->
  string -> object method pos : Loc.position method name : string end

class ['a] node_positioned :
  ?pos:Loc.position ->
  'a -> object method pos : Loc.position method node : 'a end

class ptype :
  ?pos:Loc.position ->
  ptype_node ->
  object method pos : Loc.position method node : ptype_node end

class pexpr :
  ?pos:Loc.position ->
  pexpr_node ->
  object method pos : Loc.position method node : pexpr_node end

class pexpr_with :
  ?pos:Loc.position ->
  ?node:pexpr_node ->
  < pos : Loc.position; node : pexpr_node; .. > -> pexpr

class nexpr :
  ?pos:Loc.position ->
  ?label:label ->
  nexpr_node ->
  object
    val mutable llab : label option
    method pos : Loc.position
    method label : label option
    method node : nexpr_node
    method set_label : label option -> unit
  end

class pattern :
  ?pos:Loc.position ->
  typ:jc_type ->
  pattern_node ->
  object
    method pos : Loc.position
    method node : pattern_node
    method typ : jc_type
  end

class term :
  ?pos:Loc.position ->
  typ:jc_type ->
  ?mark:string ->
  ?label:label ->
  ?region:region ->
  term_node ->
  object
    val mutable r : region
    method pos : Loc.position
    method mark : string
    method node : term_node
    method region : region
    method set_region : region -> unit
    method label : label option
    method set_label : label option -> unit
    method typ : jc_type
  end

class term_with :
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?mark:string ->
  ?region:region ->
  ?node:term_node ->
  < pos : Loc.position; mark : string; node : term_node;
    label: label option;
    region : region; typ : jc_type; .. > ->
  term

val term_with_node :
  < pos : Loc.position;
    typ : jc_type;
    mark : string;
    region : region;
    label: label option; .. > ->
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?mark:string ->
  ?region:region ->
  term_node ->
  term

val term_with_node_nomark :
  < pos : Loc.position;
    typ : jc_type;
    region : region;
    label: label option; .. > ->
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?mark:string ->
  ?region:region ->
  term_node ->
  term

class term_var :
  ?pos:Loc.position -> ?mark:string -> var_info -> term

class location :
  ?pos:Loc.position ->
  typ:jc_type ->
  ?label:label ->
  ?region:region ->
  location_node ->
  object
    val mutable r : region
    method pos : Loc.position
    method typ : jc_type
    method node : location_node
    method region : region
    method set_region : region -> unit
    method label : label option
    method set_label : label option -> unit
  end

class location_with :
  ?pos:Loc.position ->
  typ:jc_type ->
  ?label:label ->
  ?region:region ->
  node:location_node ->
  < pos : Loc.position; region : region; .. > ->
  location

val location_with_node :
  < pos : Loc.position; region : region; label : label option; typ : jc_type; .. > ->
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?label:label ->
  ?region:region ->
  location_node ->
  location

class location_set :
  ?pos:Loc.position ->
  typ:jc_type ->
  ?label:label ->
  ?region:region ->
  location_set_node ->
  object
    val mutable r : region
    method pos : Loc.position
    method typ : jc_type
    method node : location_set_node
    method region : region
    method set_region : region -> unit
    method label : label option
    method set_label : label option -> unit
  end

class location_set_with :
  ?pos:Loc.position ->
  typ:jc_type ->
  ?label:label ->
  ?region:region ->
  node:location_set_node ->
  < pos : Loc.position; region : region; .. > ->
  location_set

val location_set_with_node :
  < pos : Loc.position; region : region; label : label option; typ : jc_type; .. > ->
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?label:label ->
  ?region:region ->
  location_set_node ->
  location_set

class expr :
  ?pos:Loc.position ->
  typ:jc_type ->
  ?mark:string ->
  ?region:region ->
  ?original_type:jc_type ->
  expr_node ->
  object
    val mutable r : region
    method pos : Loc.position
    method mark : string
    method node : expr_node
    method original_type : jc_type
    method region : region
    method set_region : region -> unit
    method typ : jc_type
  end
class expr_with :
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?mark:string ->
  ?region:region ->
  ?node:expr_node ->
  ?original_type:jc_type ->
  < pos : Loc.position; mark : string; node : expr_node;
    original_type : jc_type; region : region;
    typ : jc_type; .. > ->
  expr


val expr_with_node :
  < pos : Loc.position; mark : string; node : expr_node;
    original_type : jc_type; region : region;
    typ : jc_type; .. > ->
  ?pos:Loc.position ->
  ?typ:jc_type ->
  ?mark:string ->
  ?region:region ->
  ?original_type:jc_type ->
  expr_node ->
  expr

class assertion :
  ?mark:string ->
  ?label:label ->
  ?pos:Loc.position ->
  assertion_node ->
  object
    method pos : Loc.position
    method mark : string
    method label : label option
    method set_label : label option -> unit
    method node : assertion_node
  end


class assertion_with :
  ?pos:Loc.position ->
  ?mark:string ->
  ?node:assertion_node ->
  < pos : Loc.position; mark : string; node : assertion_node;
    label: label option;
    .. > ->
  assertion

val assertion_with_node :
  < pos : Loc.position;
    mark : string;
    .. > ->
  ?pos:Loc.position ->
  ?mark:string ->
  assertion_node ->
  assertion

class ['a] ptag :
  ?pos:Loc.position ->
  'a ptag_node ->
  object method pos : Loc.position method node : 'a ptag_node end

class ['a] ptag_with :
  ?pos:Loc.position ->
  ?node:'a ptag_node ->
  < pos : Loc.position; node : 'a ptag_node; .. > -> ['a] ptag

class tag :
  ?pos:Loc.position ->
  tag_node ->
  object method pos : Loc.position method node : tag_node end

class tag_with :
  ?pos:Loc.position ->
  ?node:tag_node ->
  < pos : Loc.position; node : tag_node; .. > -> tag

class ['a] decl :
  ?pos:Loc.position ->
  'a decl_node ->
  object method pos : Loc.position method node : 'a decl_node end

module PExpr :
  sig

    val mkconst : const:const -> ?pos:Loc.position -> unit -> pexpr

    val mkvoid : ?pos:Loc.position -> unit -> pexpr

    val mknull : ?pos:Loc.position -> unit -> pexpr

    val mkboolean : value:bool -> ?pos:Loc.position -> unit -> pexpr

    val mkint :
      ?value:int -> ?valuestr:string -> ?pos:Loc.position -> unit -> pexpr

    val mkbinary :
      expr1:pexpr ->
      op:bin_op ->
      expr2:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkand :
      ?expr1:pexpr ->
      ?expr2:pexpr ->
      ?list:pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mkor :
      ?expr1:pexpr ->
      ?expr2:pexpr ->
      ?list:pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mkadd :
      ?expr1:pexpr ->
      ?expr2:pexpr ->
      ?list:pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mklabel :
      label:string -> expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkvar : name:string -> ?pos:Loc.position -> unit -> pexpr

    val mkderef :
      expr:pexpr -> field:string -> ?pos:Loc.position -> unit -> pexpr

    val mkunary :
      expr:pexpr ->
      op:pexpr_unary_op -> ?pos:Loc.position -> unit -> pexpr

    val mkapp :
      fun_name:string ->
      ?labels:label list ->
      ?args:pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mkassign :
      location:pexpr ->
      value:pexpr ->
      ?field:string ->
      ?op:bin_op -> ?pos:Loc.position -> unit -> pexpr

    val mkinstanceof :
      expr:pexpr -> typ:string -> ?pos:Loc.position -> unit -> pexpr

    val mkcast :
      expr:pexpr -> typ:ptype -> ?pos:Loc.position -> unit -> pexpr

    val mkquantifier :
      quantifier:quantifier ->
      typ:ptype ->
      vars:identifier list ->
      ?triggers:pexpr list list ->
      body:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkforall :
      typ:ptype ->
      vars:identifier list ->
      ?triggers:pexpr list list ->
      body:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkat :
      expr:pexpr ->
      label:label -> ?pos:Loc.position -> unit -> pexpr

    val mkoffset_min :
      expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkoffset_max :
      expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkfresh :
      oldlab:label -> label:label -> expr:pexpr -> len:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkif :
      condition:pexpr ->
      expr_then:pexpr ->
      ?expr_else:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkblock :
      exprs:pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mklet :
      ?typ:ptype ->
      var:string ->
      ?init:pexpr ->
      body:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mklet_nodecl :
      ?typ:ptype ->
      var:string ->
      ?init:pexpr ->
      body:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkrange :
      ?left:pexpr ->
      ?right:pexpr ->
      ?locations:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkalloc :
      ?count:pexpr -> typ:string -> ?pos:Loc.position -> unit -> pexpr

    val mkreinterpret :
      expr:pexpr -> typ:string -> ?pos:Loc.position -> unit -> pexpr

    val mkassert : ?behs:identifier list -> expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkwhile :
      ?condition:pexpr ->
      ?behaviors:pexpr loopbehavior list ->
      ?variant:(pexpr * identifier option) ->
      body:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkfor :
      ?inits:pexpr list ->
      ?condition:pexpr ->
      ?updates:pexpr list ->
      ?behaviors:pexpr loopbehavior list ->
      ?variant:(pexpr * identifier option) ->
      body:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkreturn : ?expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkbreak : ?label:string -> ?pos:Loc.position -> unit -> pexpr

    val mkcontinue : ?label:string -> ?pos:Loc.position -> unit -> pexpr

    val mktry :
      expr:pexpr ->
      ?catches:(identifier * string * pexpr) list ->
      ?finally:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkthrow :
      exn:identifier ->
      ?argument:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkswitch :
      expr:pexpr ->
      ?cases:(pexpr option list * pexpr) list ->
      ?pos:Loc.position -> unit -> pexpr

    val mkcatch :
      exn:'a ->
      ?name:string ->
      ?body:pexpr -> ?pos:Loc.position -> unit -> 'a * string * pexpr

    val mkshift :
      expr:pexpr ->
      offset:pexpr ->
      ?list:pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mknot : expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkeq :
      expr1:pexpr ->
      expr2:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkimplies :
      expr1:pexpr ->
      expr2:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkiff :
      expr1:pexpr ->
      expr2:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkcontract :
      requires:pexpr option ->
      decreases:(pexpr * Ast.identifier option) option ->
      behaviors:pexpr pbehavior list ->
      expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

  end

module NExpr :
  sig
    val mkcast :
      expr:nexpr -> typ:ptype -> ?pos:Loc.position -> unit -> nexpr
  end

module PDecl :
  sig
    val mkfun_def :
      ?result_type:ptype ->
      name:identifier ->
      ?params:(bool * ptype * string) list ->
      ?clauses:'a clause list ->
      ?body:'a ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mklemma_def :
      name:string ->
      ?axiom:bool ->
      ?poly_args:string list ->
      ?labels:label list ->
      body:'a ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mklogic_var_def :
      typ:ptype ->
      name:string ->
      ?body:'a ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mklogic_def :
      ?typ:ptype ->
      name:string ->
      ?poly_args:string list ->
      ?labels:label list ->
      ?params:(ptype * string) list ->
      ?reads:'a list ->
      ?body:'a ->
      ?inductive:(identifier * label list * 'a) list ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkaxiomatic :
      name:string ->
      decls:'a Ast.decl list ->
      ?pos:Loc.position ->
      unit -> 'a decl_node node_positioned

    val mklogic_type :
      ?args:string list ->
      name:string ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkvar_def :
      typ:ptype ->
      name:string ->
      ?init:'a ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkglobal_inv_def :
      name:string ->
      body:'a ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mktag_def :
      name:string ->
      ?params:string list ->
      ?super:string * ptype list ->
      ?fields:(field_modifiers * ptype * string * int) list ->
      ?invariants:(identifier * string * 'a) list ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkenum_type_def :
      name:string ->
      left:Num.num ->
      right:Num.num ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkexception_def :
      name:string ->
      ?arg_type:ptype ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkvariant_type_def :
      name:string ->
      ?tags:identifier list ->
      ?pos:Loc.position -> unit -> 'a decl_node node_positioned

    val mkbehavior :
      ?pos:Loc.position ->
      name:string ->
      ?throws:identifier ->
      ?assumes:pexpr ->
      ?requires:pexpr ->
      ?assigns:Loc.position * pexpr list ->
      ?allocates:Loc.position * pexpr list ->
      ?ensures:pexpr -> unit -> pexpr pbehavior

    val mkrequires_clause : 'a -> 'a clause

    val mkdecreases_clause : ?measure:identifier -> 'a -> 'a clause

    val mkbehavior_clause :
      ?pos:Loc.position ->
      name:string ->
      ?throws:identifier ->
      ?assumes:pexpr ->
      ?requires:pexpr ->
      ?assigns:Loc.position * pexpr list ->
      ?allocates:Loc.position * pexpr list ->
      ?ensures:pexpr -> unit -> pexpr clause

    val mkassigns :
      ?pos:Loc.position ->
      ?locations:'a list -> unit -> Loc.position * 'a list

  end


module Expr :
  sig
    val mk :
      ?pos:Loc.position ->
      typ:jc_type ->
      ?mark:string ->
      ?region:region ->
      ?original_type:jc_type -> node:expr_node -> unit -> expr
    val mkint :
      ?value: int ->
      ?valuestr:string ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:region ->
      ?original_type:jc_type -> unit -> expr
    val mkbinary :
      expr1:expr ->
      op:expr_bin_op ->
      expr2:expr ->
      ?pos:Loc.position ->
      typ:jc_type ->
      ?mark:string ->
      ?region:region ->
      ?original_type:jc_type -> unit -> expr
    val mklet :
      var:var_info ->
      ?init:expr ->
      body:expr ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:region -> ?original_type:jc_type -> unit -> expr
    val mkvar :
      var:var_info ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:region -> ?original_type:jc_type -> unit -> expr
    val is_app : < node : expr_node; .. > -> bool
  end



module Term :
  sig
    val mkconst :
      const: const ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:Env.region ->
      unit ->
      term
    val mkint :
      ?value: int ->
      ?valuestr:string ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:region -> unit -> term
    val mkbinary :
      term1:term ->
      op:term_bin_op ->
      term2:term ->
      ?pos:Loc.position ->
      typ:jc_type ->
      ?mark:string ->
      ?region:region -> unit -> term
    val mkvar :
      var:var_info ->
      ?pos:Loc.position ->
      ?mark:string -> ?region:region -> unit -> term
  end

module Assertion :
  sig

    val is_true : assertion -> bool
    val is_false : assertion -> bool

    val mktrue : ?pos:Loc.position -> ?mark:string -> unit -> assertion

    val mkfalse :
      ?pos:Loc.position -> ?mark:string -> unit -> assertion

    val mkand :
      conjuncts:assertion list ->
      ?pos:Loc.position -> ?mark:string -> unit -> assertion

    val mkor :
      disjuncts:assertion list ->
      ?pos:Loc.position -> ?mark:string -> unit -> assertion

    val mknot :
      asrt:assertion ->
      ?pos:Loc.position -> ?mark:string -> unit -> assertion

  end
