(*
class positioned :
  pos:Loc.position option -> object method pos : Loc.position end
class typed : typ:Jc_env.jc_type -> object method typ : Jc_env.jc_type end
class labeled :
  label:Jc_env.label option ->
  object
    val mutable llab : Jc_env.label option
    method label : Jc_env.label option
    method set_label : Jc_env.label option -> unit
  end
class marked :
  mark:string -> object method mark : string end
class regioned :
  region:Jc_env.region ->
  object
    val mutable r : Jc_env.region
    method region : Jc_env.region
    method set_region : Jc_env.region -> unit
  end
*)


class identifier :
  ?pos:Loc.position ->
  string -> object method pos : Loc.position method name : string end

class ['a] node_positioned :
  ?pos:Loc.position ->
  'a -> object method pos : Loc.position method node : 'a end

class ptype :
  ?pos:Loc.position ->
  Jc_ast.ptype_node ->
  object method pos : Loc.position method node : Jc_ast.ptype_node end

class pexpr :
  ?pos:Loc.position ->
  Jc_ast.pexpr_node ->
  object method pos : Loc.position method node : Jc_ast.pexpr_node end

class pexpr_with :
  ?pos:Loc.position ->
  ?node:Jc_ast.pexpr_node ->
  < pos : Loc.position; node : Jc_ast.pexpr_node; .. > -> pexpr

class nexpr :
  ?pos:Loc.position ->
  ?label:Jc_env.label ->
  Jc_ast.nexpr_node ->
  object
    val mutable llab : Jc_env.label option
    method pos : Loc.position
    method label : Jc_env.label option
    method node : Jc_ast.nexpr_node
    method set_label : Jc_env.label option -> unit
  end

(*
class nexpr_with :
  ?pos:Loc.position ->
  ?node:Jc_ast.nexpr_node ->
  < pos : Loc.position; label : Jc_env.label;
    node : Jc_ast.nexpr_node; .. > ->
  nexpr
*)

class pattern :
  ?pos:Loc.position ->
  typ:Jc_env.jc_type ->
  Jc_ast.pattern_node ->
  object
    method pos : Loc.position
    method node : Jc_ast.pattern_node
    method typ : Jc_env.jc_type
  end

(*
class pattern_with :
  ?pos:Loc.position ->
  ?node:Jc_ast.pattern_node ->
  ?typ:Jc_env.jc_type ->
  < pos : Loc.position; node : Jc_ast.pattern_node; typ : Jc_env.jc_type;
    .. > ->
  pattern
*)


class term :
  ?pos:Loc.position ->
  typ:Jc_env.jc_type ->
  ?mark:string ->
  ?label:Jc_env.label ->
  ?region:Jc_env.region ->
  Jc_ast.term_node ->
  object
    val mutable r : Jc_env.region
    method pos : Loc.position
    method mark : string
    method node : Jc_ast.term_node
    method region : Jc_env.region
    method set_region : Jc_env.region -> unit
    method label : Jc_env.label option
    method set_label : Jc_env.label option -> unit
    method typ : Jc_env.jc_type
  end

class term_with :
  ?pos:Loc.position ->
  ?typ:Jc_env.jc_type ->
  ?mark:string ->
  ?region:Jc_env.region ->
  ?node:Jc_ast.term_node ->
  < pos : Loc.position; mark : string; node : Jc_ast.term_node;
    label: Jc_env.label option; 
    region : Jc_env.region; typ : Jc_env.jc_type; .. > ->
  term

class term_var :
  ?pos:Loc.position -> ?mark:string -> Jc_env.var_info -> term

class location :
  ?pos:Loc.position ->
  ?label:Jc_env.label ->
  ?region:Jc_env.region ->
  Jc_ast.location_node ->
  object
    val mutable r : Jc_env.region
    method pos : Loc.position
    method node : Jc_ast.location_node
    method region : Jc_env.region
    method set_region : Jc_env.region -> unit
    method label : Jc_env.label option
    method set_label : Jc_env.label option -> unit
  end

class location_with :
  ?pos:Loc.position ->
  ?region:Jc_env.region ->
  ?node:Jc_ast.location_node ->
  < pos : Loc.position; node : Jc_ast.location_node;
    label: Jc_env.label option; 
    region : Jc_env.region; .. > ->
  location

class location_set :
  ?pos:Loc.position ->
  ?label:Jc_env.label ->
  ?region:Jc_env.region ->
  Jc_ast.location_set_node ->
  object
    val mutable r : Jc_env.region
    method pos : Loc.position
    method node : Jc_ast.location_set_node
    method region : Jc_env.region
    method set_region : Jc_env.region -> unit
    method label : Jc_env.label option
    method set_label : Jc_env.label option -> unit
  end

class location_set_with :
  ?pos:Loc.position ->
  ?region:Jc_env.region ->
  ?node:Jc_ast.location_set_node ->
  < pos : Loc.position; node : Jc_ast.location_set_node;
    label: Jc_env.label option; 
    region : Jc_env.region; .. > ->
  location_set

class expr :
  ?pos:Loc.position ->
  typ:Jc_env.jc_type ->
  ?mark:string ->
  ?region:Jc_env.region ->
  ?original_type:Jc_env.jc_type ->
  Jc_ast.expr_node ->
  object
    val mutable r : Jc_env.region
    method pos : Loc.position
    method mark : string
    method node : Jc_ast.expr_node
    method original_type : Jc_env.jc_type
    method region : Jc_env.region
    method set_region : Jc_env.region -> unit
    method typ : Jc_env.jc_type
  end
class expr_with :
  ?pos:Loc.position ->
  ?typ:Jc_env.jc_type ->
  ?mark:string ->
  ?region:Jc_env.region ->
  ?node:Jc_ast.expr_node ->
  ?original_type:Jc_env.jc_type ->
  < pos : Loc.position; mark : string; node : Jc_ast.expr_node;
    original_type : Jc_env.jc_type; region : Jc_env.region;
    typ : Jc_env.jc_type; .. > ->
  expr


class assertion :
  ?mark:string ->
  ?label:Jc_env.label ->
  ?pos:Loc.position ->
  Jc_ast.assertion_node ->
  object
    method pos : Loc.position
    method mark : string
    method label : Jc_env.label option
    method set_label : Jc_env.label option -> unit
    method node : Jc_ast.assertion_node
  end


class assertion_with :
  ?pos:Loc.position ->
  ?mark:string ->
  ?node:Jc_ast.assertion_node ->
  < pos : Loc.position; mark : string; node : Jc_ast.assertion_node;
    label: Jc_env.label option;
    .. > ->
  assertion

class ['a] ptag :
  ?pos:Loc.position ->
  'a Jc_ast.ptag_node ->
  object method pos : Loc.position method node : 'a Jc_ast.ptag_node end

class ['a] ptag_with :
  ?pos:Loc.position ->
  ?node:'a Jc_ast.ptag_node ->
  < pos : Loc.position; node : 'a Jc_ast.ptag_node; .. > -> ['a] ptag

class tag :
  ?pos:Loc.position ->
  Jc_ast.tag_node ->
  object method pos : Loc.position method node : Jc_ast.tag_node end

class tag_with :
  ?pos:Loc.position ->
  ?node:Jc_ast.tag_node ->
  < pos : Loc.position; node : Jc_ast.tag_node; .. > -> tag

class ['a] decl :
  ?pos:Loc.position ->
  'a Jc_ast.decl_node ->
  object method pos : Loc.position method node : 'a Jc_ast.decl_node end

(*

class ['a] decl_with :
  ?pos:Loc.position ->
  ?node:'a Jc_ast.decl_node ->
  < pos : Loc.position; node : 'a Jc_ast.decl_node; .. > -> ['a] decl
module Const :
  sig
    val mkvoid : Jc_ast.const
    val mknull : Jc_ast.const
    val mkboolean : bool -> Jc_ast.const
    val mkint : ?value:int -> ?valuestr:string -> unit -> Jc_ast.const
    val mkreal : ?value:float -> ?valuestr:string -> unit -> Jc_ast.const
  end
val oo : 'a option -> 'a -> 'a
*)

module PExpr :
  sig
(*
    val mk : ?pos:Loc.position -> node:Jc_ast.pexpr_node -> unit -> pexpr
*)
    val mkconst : const:Jc_ast.const -> ?pos:Loc.position -> unit -> pexpr

    val mkvoid : ?pos:Loc.position -> unit -> pexpr

    val mknull : ?pos:Loc.position -> unit -> pexpr

    val mkboolean : value:bool -> ?pos:Loc.position -> unit -> pexpr

    val mkint :
      ?value:int -> ?valuestr:string -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkreal :
      ?value:float -> ?valuestr:string -> ?pos:Loc.position -> unit -> pexpr
*)
    val mkbinary :
      expr1:Jc_ast.pexpr ->
      op:Jc_ast.bin_op ->
      expr2:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
(*
    val mkbinary_list :
      default:Jc_ast.pexpr ->
      op:Jc_ast.bin_op ->
      ?expr1:Jc_ast.pexpr ->
      ?expr2:Jc_ast.pexpr ->
      ?list:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> Jc_ast.pexpr
*)
    val mkand :
      ?expr1:Jc_ast.pexpr ->
      ?expr2:Jc_ast.pexpr ->
      ?list:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> Jc_ast.pexpr

    val mkor :
      ?expr1:Jc_ast.pexpr ->
      ?expr2:Jc_ast.pexpr ->
      ?list:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> Jc_ast.pexpr

    val mkadd :
      ?expr1:Jc_ast.pexpr ->
      ?expr2:Jc_ast.pexpr ->
      ?list:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> Jc_ast.pexpr

    val mklabel :
      label:string -> expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkvar : name:string -> ?pos:Loc.position -> unit -> pexpr

    val mkderef :
      expr:Jc_ast.pexpr -> field:string -> ?pos:Loc.position -> unit -> pexpr

    val mkunary :
      expr:Jc_ast.pexpr ->
      op:Jc_ast.pexpr_unary_op -> ?pos:Loc.position -> unit -> pexpr

    val mkapp :
      fun_name:string ->
      ?labels:Jc_env.label list ->
      ?args:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> pexpr

    val mkassign :
      location:Jc_ast.pexpr ->
      value:Jc_ast.pexpr ->
      ?field:string ->
      ?op:Jc_ast.bin_op -> ?pos:Loc.position -> unit -> pexpr

    val mkinstanceof :
      expr:Jc_ast.pexpr -> typ:string -> ?pos:Loc.position -> unit -> pexpr

    val mkcast :
      expr:Jc_ast.pexpr -> typ:string -> ?pos:Loc.position -> unit -> pexpr

    val mkquantifier :
      quantifier:Jc_ast.quantifier ->
      typ:Jc_ast.ptype ->
      vars:string list ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkforall :
      typ:Jc_ast.ptype ->
      vars:string list ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkexists :
      typ:Jc_ast.ptype ->
      vars:string list ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
    val mkold : expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
*)

    val mkat :
      expr:Jc_ast.pexpr ->
      label:Jc_env.label -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkoffset :
      kind:Jc_ast.offset_kind ->
      expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
    val mkoffset_min :
      expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
*)

    val mkoffset_max :
      expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkif :
      condition:Jc_ast.pexpr ->
      expr_then:Jc_ast.pexpr ->
      ?expr_else:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkblock :
      exprs:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkdecl :
      typ:Jc_ast.ptype ->
      var:string -> ?init:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
*)
    val mklet :
      ?typ:Jc_ast.ptype ->
      var:string ->
      ?init:Jc_ast.pexpr ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mklet_nodecl :
      ?typ:Jc_ast.ptype ->
      var:string ->
      ?init:Jc_ast.pexpr ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkrange :
      ?left:Jc_ast.pexpr ->
      ?right:Jc_ast.pexpr ->
      ?locations:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkalloc :
      ?count:pexpr -> typ:string -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkfree : expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr
    val mkmutable :
      expr:Jc_ast.pexpr ->
      tag:Jc_ast.pexpr Jc_ast.ptag -> ?pos:Loc.position -> unit -> pexpr
    val mktag_equality :
      tag1:Jc_ast.pexpr Jc_ast.ptag ->
      tag2:Jc_ast.pexpr Jc_ast.ptag -> ?pos:Loc.position -> unit -> pexpr
    val mkmatch :
      expr:Jc_ast.pexpr ->
      cases:(Jc_ast.ppattern * Jc_ast.pexpr) list ->
      ?pos:Loc.position -> unit -> pexpr
*)

    val mkassert : expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkwhile :
      ?condition:pexpr ->
      ?invariant:(string list * Jc_ast.pexpr) list ->
      ?variant:Jc_ast.pexpr ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkfor :
      ?inits:Jc_ast.pexpr list ->
      ?condition:pexpr ->
      ?updates:Jc_ast.pexpr list ->
      ?invariant:pexpr ->
      ?variant:Jc_ast.pexpr ->
      body:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkreturn : ?expr:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkbreak : ?label:string -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkcontinue : ?label:string -> ?pos:Loc.position -> unit -> pexpr
    val mkgoto : label:string -> ?pos:Loc.position -> unit -> pexpr

*)

    val mktry :
      expr:Jc_ast.pexpr ->
      ?catches:(Jc_ast.identifier * string * Jc_ast.pexpr) list ->
      ?finally:pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkthrow :
      exn:Jc_ast.identifier ->
      ?argument:pexpr -> ?pos:Loc.position -> unit -> pexpr

(*
    val mkpack :
      expr:Jc_ast.pexpr ->
      ?tag:Jc_ast.identifier -> ?pos:Loc.position -> unit -> pexpr
    val mkunpack :
      expr:Jc_ast.pexpr ->
      ?tag:Jc_ast.identifier -> ?pos:Loc.position -> unit -> pexpr
*)

    val mkswitch :
      expr:Jc_ast.pexpr ->
      ?cases:(Jc_ast.pexpr option list * Jc_ast.pexpr) list ->
      ?pos:Loc.position -> unit -> pexpr

    val mkcatch :
      exn:'a ->
      ?name:string ->
      ?body:pexpr -> ?pos:Loc.position -> unit -> 'a * string * pexpr

    val mkshift :
      expr:Jc_ast.pexpr ->
      offset:Jc_ast.pexpr ->
      ?list:Jc_ast.pexpr list -> ?pos:Loc.position -> unit -> Jc_ast.pexpr

    val mknot : expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkeq :
      expr1:Jc_ast.pexpr ->
      expr2:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkimplies :
      expr1:Jc_ast.pexpr ->
      expr2:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkiff :
      expr1:Jc_ast.pexpr ->
      expr2:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

    val mkincr_heap :
      expr:Jc_ast.pexpr ->
      field:string ->
      ?op:Jc_ast.pexpr_unary_op -> ?pos:Loc.position -> unit -> pexpr

    val mkcontract : 
      requires:Jc_ast.pexpr option ->
      decreases:Jc_ast.pexpr option ->
      behaviors:Jc_ast.pexpr Jc_ast.pbehavior list ->
      expr:Jc_ast.pexpr -> ?pos:Loc.position -> unit -> pexpr

  end

module NExpr :
  sig
    val mkcast :
      expr:Jc_ast.nexpr -> typ:string -> ?pos:Loc.position -> unit -> nexpr
  end

module PDecl :
  sig
(*
    val mk : ?pos:Loc.position -> node:'a -> unit -> 'a node_positioned
*)

    val mkfun_def :
      ?result_type:ptype ->
      name:Jc_ast.identifier ->
      ?params:(Jc_ast.ptype * string) list ->
      ?clauses:'a Jc_ast.clause list ->
      ?body:'a ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mklemma_def :
      name:string ->
      ?axiom:bool ->
      ?labels:Jc_env.label list ->
      body:'a ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mklogic_var_def :
      typ:Jc_ast.ptype ->
      name:string ->
      ?body:'a ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mklogic_def :
      ?typ:Jc_ast.ptype ->
      name:string ->
      ?labels:Jc_env.label list ->
      ?params:(Jc_ast.ptype * string) list ->
      ?reads:'a list ->
      ?body:'a ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mklogic_type :
      name:string ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkvar_def :
      typ:Jc_ast.ptype ->
      name:string ->
      ?init:'a ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkglobal_inv_def :
      name:string ->
      body:'a ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mktag_def :
      name:string ->
      ?params:string list ->
      ?super:string * Jc_ast.ptype list ->
      ?fields:(bool * Jc_ast.ptype * string * int option) list ->
      ?invariants:(Jc_ast.identifier * string * 'a) list ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkenum_type_def :
      name:string ->
      left:Num.num ->
      right:Num.num ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkexception_def :
      name:string ->
      ?arg_type:Jc_ast.ptype ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkvariant_type_def :
      name:string ->
      ?tags:Jc_ast.identifier list ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkinvariant_policy_def :
      value:Jc_env.inv_sem ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkseparation_policy_def :
      value:Jc_env.separation_sem ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkannotation_policy_def :
      value:Jc_env.annotation_sem ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

    val mkabstract_domain_def :
      value:Jc_env.abstract_domain ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

(*

    val mkint_model_def :
      value:Jc_env.int_model ->
      ?pos:Loc.position -> unit -> 'a Jc_ast.decl_node node_positioned

*)

    val mkbehavior :
      ?pos:Loc.position ->
      name:string ->
      ?throws:Jc_ast.identifier ->
      ?assumes:pexpr ->
      ?requires:pexpr ->
      ?assigns:Loc.position * pexpr list ->
      ?ensures:pexpr -> unit -> pexpr Jc_ast.pbehavior

    val mkrequires_clause : 'a -> 'a Jc_ast.clause

    val mkbehavior_clause :
      ?pos:Loc.position ->
      name:string ->
      ?throws:Jc_ast.identifier ->
      ?assumes:pexpr ->
      ?requires:pexpr ->
      ?assigns:Loc.position * pexpr list ->
      ?ensures:pexpr -> unit -> pexpr Jc_ast.clause

(*
    val mkbehavior_with :
      ?pos:Loc.position ->
      ?name:string ->
      ?throws:Jc_ast.identifier option ->
      ?assumes:'a option ->
      ?requires:'a option ->
      ?assigns:(Loc.position * 'a list) option ->
      ?ensures:'a -> 'a Jc_ast.clause -> 'a Jc_ast.clause
*)

    val mkassigns :
      ?pos:Loc.position ->
      ?locations:'a list -> unit -> Loc.position * 'a list

(*
    val mktag_invariant : name:'a -> var:'b -> body:'c -> 'a * 'b * 'c
    val behavior_ensures : 'a Jc_ast.clause -> 'a
*)
  end


module Expr :
  sig
    val mk :
      ?pos:Loc.position ->
      typ:Jc_env.jc_type ->
      ?mark:string ->
      ?region:Jc_env.region ->
      ?original_type:Jc_env.jc_type -> node:Jc_ast.expr_node -> unit -> expr
    val mklet :
      var:Jc_env.var_info ->
      ?init:Jc_ast.expr ->
      body:Jc_ast.expr ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:Jc_env.region -> ?original_type:Jc_env.jc_type -> unit -> expr
    val mkvar :
      var:Jc_env.var_info ->
      ?pos:Loc.position ->
      ?mark:string ->
      ?region:Jc_env.region -> ?original_type:Jc_env.jc_type -> unit -> expr
    val is_app : < node : Jc_ast.expr_node; .. > -> bool
  end



module Term :
  sig
(*
    val mk :
      ?pos:Loc.position ->
      typ:Jc_env.jc_type ->
      ?mark:string ->
      ?region:Jc_env.region -> node:Jc_ast.term_node -> unit -> term
*)

    val mkvar :
      var:Jc_env.var_info ->
      ?pos:Loc.position ->
      ?mark:string -> ?region:Jc_env.region -> unit -> term
  end

module Assertion :
  sig
(*
    val mk :
      ?pos:Loc.position ->
      ?mark:string -> node:Jc_ast.assertion_node -> unit -> assertion
    val fake : ?pos:'a -> ?mark:'b -> value:'c -> unit -> 'c
*)

    val mktrue : ?pos:Loc.position -> ?mark:string -> unit -> assertion

(*
    val mkfalse :
      ?pos:Loc.position -> ?mark:string -> unit -> assertion
*)

    val mkand :
      conjuncts:Jc_ast.assertion list ->
      ?pos:Loc.position -> ?mark:string -> unit -> assertion

  end
