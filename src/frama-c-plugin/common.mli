(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
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
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Cil
open Cil_types
open Cil_datatype
open Visitor

open Format

module Emitters :
sig
  type t = Emitter.t
  val jessie : Emitter.t
  val jessie_assume : Emitter.t
end

exception Unsupported of string

module Console :
sig
  val fatal : ('a, formatter, unit, 'b) format4 -> 'a
  val error : ('a, formatter, unit) format -> 'a
  val abort : ?source:Filepath.position -> ('a, formatter, unit, 'b) format4 -> 'a
  val unsupported : ('a, formatter, unit, 'b) format4 -> 'a
  val feedback : ('a, formatter, unit) format -> 'a
  val warning : ('a, formatter, unit) format -> 'a
  val general_warning : ('a, formatter, unit) format -> 'a
  val warn_once : string -> unit
  val debug : ('a, formatter, unit) format -> 'a
  val debug_at_least : int -> bool
  val verbose_at_least : int -> bool
end

module List :
sig
  include module type of List
  type 'a t = 'a list
  val rev_filter_map : 'a t -> f:('a -> 'b option) -> 'b t
  val filter_map : 'a t -> f:('a -> 'b option) -> 'b t
  val find_map : 'a t -> f:('a -> 'b option) -> 'b option
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val drop : int -> 'a t -> 'a t
  val take : int -> 'a t -> 'a t
  val range : int -> [< `Downto | `To ] -> int -> int t
  val groupi : break:(int -> 'a ->'a -> bool) -> 'a list -> 'a list list
  val group : break:('a -> 'a -> bool) -> 'a list -> 'a list list
end

module String :
sig
  include module type of String
  val explode : t -> char list
  val implode : char list -> t
  val filter_alphanumeric : assoc:(char * char) list -> default:char -> t -> t
end

module Tuple :
sig
  module T2 :
  sig
    type ('a, 'b) t = 'a * 'b
    val fdup2 : f:('a -> 'b) -> g:('a -> 'c) -> 'a -> 'b * 'c
    val map1 : f:('a -> 'b) -> 'a * 'c -> 'b * 'c
    val map2 : f:('a -> 'b) -> 'c * 'a -> 'c * 'b
    val map : f:('a -> 'b) -> 'a * 'a -> 'b * 'b
    val iter : f:('a -> unit) -> 'a * 'a -> unit
    val swap : 'a * 'b -> 'b * 'a
  end
end

module Pair = Tuple.T2

module Fn :
sig
  type ('a, 'b) t = 'a -> 'b
  val id : 'a -> 'a
  val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val pipe_compose : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
end

val ( % ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

val ( %> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c

val fdup2 : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c

val map_fst : ('a -> 'b) -> 'a * 'c -> 'b * 'c

val map_snd : ('a -> 'b) -> 'c * 'a -> 'c * 'b

val map_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b

val iter_pair : ('a -> unit) -> 'a * 'a -> unit

val swap : 'a * 'b -> 'b * 'a

module Monad_def :
sig
  module type S =
  sig
    type 'a m
    val return : 'a -> 'a m
    val bind : 'a m -> ('a -> 'b m) -> 'b m
  end
end

module Monad :
sig
  module type S =
  sig
    include Monad_def.S
    val ( >>= ) : 'a m -> ('a -> 'b m) -> 'b m
    val ( >> ) : 'a m -> 'b m -> 'b m
  end
  module Make : functor (M : Monad_def.S) -> S
end

module Option :
sig
  include Monad.S with type 'a m := 'a option

  val value : default:'a -> 'a option -> 'a
  val value_exn : exn:exn -> 'a option -> 'a
  val value_fatal : in_:string -> 'a option -> 'a
  val compare : cmp:('a -> 'b -> int) -> 'a option -> 'b option -> int
  val equal : eq:('a -> 'b -> bool) -> 'a option -> 'b option -> bool

  val abort : 'a option
  val map : f:('a -> 'b) -> 'a option -> 'b option
  val map_default : default:'b -> f:('a -> 'b) -> 'a option -> 'b
  val fold : init:'b -> f:('b -> 'a -> 'b) -> 'a option -> 'b
  val iter : f:('a -> unit) -> 'a option -> unit
  val is_some : 'a option -> bool
end

val ( |? ) : 'a option -> 'a -> 'a

val ( !! ) : 'a lazy_t -> 'a

module Filepath :
sig
  include module type of struct include Filepath end
  val is_unknown : Filepath.position * 'a -> bool
end

module Loc :
sig
  open Lexing
  type t = position * position
  val is_unknown : position * 'a -> bool
  val to_position : position -> Filepath.position
  val of_position : Filepath.position -> position
  val to_location : t -> Location.t
  val of_location : Location.t -> t
end

module Framac :
sig
  module Ast = Ast
  module Type = Type
  module Vi = Varinfo
  module Config = Config
end

module Config :
sig
  include module type of Jessie_options
  val flatten_multi_dim_arrays : bool
end

val mkStmt : ?ghost:bool -> stmtkind -> stmt

module Name :
sig
  module Attr :
  sig
    val embedded : string
    val noembed : string
    val packed : string
    val padding : string
    val wrapper : string
    val arraylen : string
    val string_declspec : string
  end

  module Predicate :
  sig
    val valid_string : string
    val valid_wstring : string
  end

  module Logic_function :
  sig
    val strlen : string
    val wcslen : string
    val nondet_int : string
  end

  module Function :
  sig
    val assert_ : string
    val free : string
    val kfree : string
    val kzfree : string
    val malloc : string
    val kmalloc : string
    val kzalloc : string
    val calloc : string
    val realloc : string
    val memdup : string
    val kmemdup : string
    val alloca : string
  end

  module File :
  sig
    val blockfuns_include : string
  end

  val typ : typ -> string
  val logic_type : logic_type -> string

  module Logic_type :
  sig
    val padding : string
  end

  module Behavior :
  sig
    val safety : string
    val default : string
  end

  module Jc_specific :
  sig
    val hint : string
  end

  val is_predefined : string -> bool
  val unique : ?force:bool -> string -> string

  module Logic :
  sig
    val unique : string -> string
  end

  val unique_if_empty : string -> string
end

module Ast :
sig
  module Exp :
  sig
    type t = exp
    val const : ?loc:Location.t -> Integer.t -> t
    val dummy_info : t -> t
    val strip_casts_to: typ -> exp -> exp
  end

  module rec Vi :
  sig
    type var
    type func
    type 'a t = private varinfo

    module Function :
    sig
      type t = func Vi.t

      val of_varinfo : varinfo -> t option
      val of_varinfo_exn : varinfo -> t

      val is_assert : t -> bool
      val is_free : t -> bool
      val is_kfree : t -> bool
      val is_kzfree : t -> bool
      val is_malloc : t -> bool
      val is_kmalloc : t -> bool
      val is_kzalloc : t -> bool
      val is_calloc : t -> bool
      val is_realloc : t -> bool
      val is_memdup : t -> bool
      val is_kmemdup : t -> bool
      val is_alloca : t -> bool
      val malloc : ?kernel:bool -> unit -> t
      val free : unit -> t
    end

    module Variable :
    sig
      type t = var Vi.t
      val of_varinfo : varinfo -> t option
      val of_varinfo_exn : varinfo -> t
      val pseudo : typ -> t
    end
  end

  module Term :
  sig
    type t = term
    val is_base_addr : t -> bool
    val mk : ?name:string list -> typ:logic_type -> loc:Filepath.position * Filepath.position -> term_node -> t
    val mk_loc : ?name:string list -> typ:logic_type -> loc:Lexing.position * Lexing.position -> term_node -> t
    val of_var : varinfo -> t

    module Env :
    sig
      type t
    end

    val to_exp_env : t -> Exp.t * Env.t
    val lval_to_lval_env : term_lval -> lval * Env.t
    val lhost_to_lhost_env : term_lhost -> lhost * Env.t
    val offset_to_offset_env : term_offset -> offset * Env.t
    val of_exp_env : Exp.t * Env.t -> t
    val offset_of_offset_env : offset * Env.t -> term_offset
    val lhost_of_lhost_env : lhost * Env.t -> term_lhost
    val lval_of_lval_env : lval * Env.t -> term_lval
    val of_exp : Exp.t -> t
    val offset_of_offset : offset -> term_offset
    val lhost_of_lhost : lhost -> term_lhost
    val lval_of_lval : lval -> term_lval
  end

  module Predicate :
  sig
    type t = predicate
    val mk : ?name:string list -> loc:location -> predicate_node -> t
    val of_exp_exn : Exp.t -> t
  end

  module Code_annotation :
  sig
    type t = code_annotation
    val of_exp_exn : Exp.t -> code_annotation
  end

  module Offset :
  sig
    type t = offset
    val is_last : t -> bool
    val flatten : typ:typ -> t -> t
  end

  module Instr :
  sig
    type t = instr
    val alloc_singleton : lvar:varinfo -> typ:typ -> loc:Location.t -> t
    val alloc_array : lvar:varinfo -> typ:typ -> size:int64 -> loc:Location.t -> t
    val free : loc:Location.t -> varinfo -> t
  end

  module Stmt :
  sig
    type t = stmt
    val alloc_singleton : lvar:varinfo -> typ:typ -> loc:Location.t -> t
    val alloc_array : lvar:varinfo -> typ:typ -> size:int64 -> loc:Location.t -> t
    val free : loc:Location.t -> varinfo -> t
  end
end

module rec Type :
sig
  type composite
  type integral
  type ref
  type 'a t = private typ

  module Logic_c_type :
  sig
    type t = private logic_type
    val of_logic_type : logic_type -> t option
    val of_logic_type_exn : logic_type -> t
    val map_default : default:'a -> f:(typ -> 'a) -> logic_type -> 'a
    val map : f:(typ -> 'a) -> t -> 'a
    val get : t -> typ
    val is_c : logic_type -> bool
    val typ : logic_type -> typ option
  end

  module Ref :
  sig
    type t = ref Type.t
    val singleton : msg:'a -> typ -> t
    val array : size:exp -> ?attrs:attributes -> typ -> t
    val size : t -> int64
    val of_typ : typ -> t option
    val of_typ_exn : typ -> t
    val typ : t -> typ
    val is_array : t -> bool
    val is_ref : typ -> bool
    val is_array_ref : typ -> bool
    val of_array_exn : typ -> t
  end

  module rec Composite :
  sig
    type t = composite Type.t

    val of_typ : typ -> t option
    val of_typ_exn : typ -> t
    val unique_field_exn : t -> fieldinfo
    val compinfo_cname : t -> string
    val compinfo : t -> compinfo

    module Ci :
    sig
      type t = compinfo

      module Struct :
      sig
        type t = private compinfo

        val of_ci : compinfo -> t option
        val of_ci_exn : compinfo -> t
        val empty : string -> t
        val singleton : ?padding:int -> sname:string -> fname:string -> typ -> t
      end

      val size : compinfo -> int option
      val fill_jessie_fields : compinfo -> unit
      val padding_field : fsize_in_bits:int -> compinfo -> fieldinfo
      val fix_size : ?original_size:int -> compinfo -> unit
      val proper_fields : compinfo -> fieldinfo list
    end

    module Struct :
    sig
      type t = private composite Type.t
      val of_typ : typ -> t option
      val of_typ_exn : typ -> t
      val is_struct : typ -> bool
      val void : unit -> t
      val init_void : t -> unit
      val char : unit -> t
      val init_char : t -> unit
    end
  end

  val promote_argument_type : typ -> typ
  val size_in_bits_exn : typ -> int64

  module Integral :
  sig
    type t = integral Type.t

    val of_typ : typ -> t option
    val of_typ_exn : typ -> t

    val almost_unbound : t

    module IKind :
    sig
      type t = ikind
      val size_in_bytes : ikind -> int
    end

    val int : ?attrs:attributes -> ikind -> t
    val is_signed : t -> bool

    val size_in_bytes : t -> int
    val size_in_bits : t -> int

    val min_value : ?bitsize:int -> t -> Integer.t
    val max_value : ?bitsize:int -> t -> Integer.t

    module All : State_builder.Hashtbl with type key := string and type data = t * int option

    val name : ?bitsize:int -> t -> string
    val of_bitsize_u : int * bool -> t
    val add_by_name : string -> unit
    val iter_all : (string -> All.data -> unit) -> unit
    val fold_all : (string -> All.data -> 'c -> 'c) -> 'c -> 'c
  end
end

module Do :
sig
  val retaining_size_of_composite : compinfo -> (compinfo -> 'a) -> 'a
  val retaining_size_of_field : fieldinfo -> (fieldinfo -> 'a) -> 'a

  type 'a attach = 'a
    constraint 'a =
      < globaction : (unit -> unit) -> unit;
        global : global -> unit; .. >

  type attaching_action = { perform : 'a. attach:'a attach -> file -> unit }

  val attaching_globs : attaching_action -> file -> unit

  val on_term_offset :
    ?pre:(offset -> offset) ->
    ?post:(offset -> offset) ->
    term_offset -> term_offset visitAction

  val on_term_lval :
    ?pre:(lval -> lval) ->
    ?post:(lval -> lval) ->
    term_lval -> term_lval visitAction

  val on_term :
    ?pre:(exp -> exp) ->
    ?post:(exp -> exp) ->
    term -> term visitAction
end

module Visit :
sig
  type insert

  val prepend : insert -> stmt -> insert
  val append : insert -> stmt -> insert
  val insert : insert -> before:stmt -> after:stmt -> insert

  val prepending : stmt list -> insert
  val appending : stmt list -> insert
  val inserting : before:stmt list -> after:stmt list -> insert

  val inserting_nothing : insert
  val do_nothing : 'a -> 'a * insert
  val of_action : ('a -> 'a) -> ('a -> 'a * insert)

  module Local :
  sig
    type 'a visit_action =
      | SkipChildren of insert
      | DoChildren of insert
      | DoChildrenPost of ('a -> 'a * insert) * insert
      | JustCopy of insert
      | JustCopyPost of ('a -> 'a * insert) * insert
      | ChangeTo of 'a * insert
      | ChangeToPost of 'a * ('a -> 'a * insert) * insert
      | ChangeDoChildrenPost of 'a * ('a -> 'a * insert) * insert

    val to_visit_action : 'a visitAction -> 'a visit_action
  end

  type ('a, 'result, 'visit_action) context =
    | Local : fundec -> ('a, 'a * insert, 'a Local.visit_action) context
    | Global : ('a, 'a, 'a visitAction) context

  module Fundec :
  sig
    type 'a visit_action =
      | SkipChildren of insert
      | DoChildren of insert
      | DoChildrenPost of ('a -> 'a * insert) * insert
      | JustCopy of insert
      | JustCopyPost of ('a -> 'a * insert) * insert
      | ChangeTo of 'a
      | ChangeToPost of 'a * ('a -> 'a * insert)
      | ChangeDoChildrenPost of 'a * ('a -> 'a * insert)

    val to_visit_action : 'a visitAction -> 'a visit_action
  end

  val to_visit_action : 'a visitAction -> ('a, 'b, 'c) context -> 'c

  type ('a, 'r, 'v) visitor_method = 'a -> ('a, 'r, 'v) context -> 'v

  class frama_c_inplace_inserting :
    #frama_c_visitor ->
    object
      method behavior : visitor_behavior
      method current_func : fundec option
      method current_kf : kernel_function option
      method current_kinstr : kinstr
      method current_stmt : stmt option
      method fill_global_tables : unit
      method frama_c_plain_copy : frama_c_visitor
      method get_filling_actions : (unit -> unit) Queue.t
      method plain_copy_visitor : cilVisitor
      method pop_stmt : stmt -> unit
      method project : Project_skeleton.t option
      method push_stmt : stmt -> unit
      method queueInstr : instr list -> unit
      method reset_current_func : unit -> unit
      method reset_current_kf : unit -> unit
      method set_current_func : fundec -> unit
      method set_current_kf : kernel_function -> unit
      method unqueueInstr : unit -> instr list
      method vallocates : (identified_term list, 'a, 'b) visitor_method
      method vallocation : (allocation, 'a, 'b) visitor_method
      method vannotation :  global_annotation -> global_annotation visitAction
      method vassigns : (assigns, 'a, 'b) visitor_method
      method vattr : attribute list -> (attribute list, 'a, 'b) context -> 'b
      method vattrparam : (attrparam, 'a, 'b) visitor_method
      method vbehavior : (funbehavior, 'a, 'b) visitor_method
      method vblock : block -> fundec -> block Local.visit_action
      method vcode_annot : code_annotation -> fundec -> code_annotation Local.visit_action
      method vcompinfo : compinfo -> compinfo visitAction
      method vdeps : (deps, 'a, 'b) visitor_method
      method venuminfo : enuminfo -> enuminfo visitAction
      method venumitem : enumitem -> enumitem visitAction
      method vexpr : (exp, 'a, 'b) visitor_method
      method vfieldinfo : fieldinfo -> fieldinfo visitAction
      method vfile : file -> file visitAction
      method vfrees : (identified_term list, 'a, 'b) visitor_method
      method vfrom : (from, 'a, 'b) visitor_method
      method vfunc : fundec -> fundec Fundec.visit_action
      method vglob : global -> global list visitAction
      method vglob_aux : global -> global list Cil.visitAction
      method videntified_predicate : (identified_predicate, 'a, 'b) visitor_method
      method videntified_term : (identified_term, 'a, 'b) visitor_method
      method vimpact_pragma : (impact_pragma, 'a, 'b) visitor_method
      method vinit : varinfo -> offset -> init -> (init, 'a, 'b) context -> 'b
      method vinitoffs : (offset, 'a, 'b) visitor_method
      method vinst : instr -> fundec -> instr list Local.visit_action
      method vjessie_pragma : jessie_pragma -> fundec -> jessie_pragma Local.visit_action
      method vlogic_ctor_info_decl : logic_ctor_info -> logic_ctor_info visitAction
      method vlogic_ctor_info_use : (logic_ctor_info, 'a, 'b) visitor_method
      method vlogic_info_decl : logic_info -> logic_info visitAction
      method vlogic_info_use : (logic_info, 'a, 'b) visitor_method
      method vlogic_label : (logic_label, 'a, 'b) visitor_method
      method vlogic_type : (logic_type, 'a, 'b) visitor_method
      method vlogic_type_def : logic_type_def -> logic_type_def visitAction
      method vlogic_type_info_decl : logic_type_info -> logic_type_info visitAction
      method vlogic_type_info_use : (logic_type_info, 'a, 'b) visitor_method
      method vlogic_var_decl : (logic_var, 'a, 'b) visitor_method
      method vlogic_var_use : (logic_var, 'a, 'b) visitor_method
      method vloop_pragma : loop_pragma -> fundec -> loop_pragma Local.visit_action
      method vlval : (lval, 'a, 'b) visitor_method
      method vmodel_info : model_info -> model_info visitAction
      method voffs : (offset, 'a, 'b) visitor_method
      method vpredicate_node : (predicate_node, 'a, 'b) visitor_method
      method vpredicate : (predicate, 'a, 'b) visitor_method
      method vquantifiers : (quantifiers, 'a, 'b) visitor_method
      method vslice_pragma : (slice_pragma, 'a, 'b) visitor_method
      method vspec : (funspec, 'a, 'b) visitor_method
      method vstmt : stmt -> stmt visitAction
      method vstmt_aux_inserting : stmt -> fundec -> stmt Local.visit_action
      method vterm : (term, 'a, 'b) visitor_method
      method vterm_lhost : (term_lhost, 'a, 'b) visitor_method
      method vterm_lval : (term_lval, 'a, 'b) visitor_method
      method vterm_node : (term_node, 'a, 'b) visitor_method
      method vterm_offset : (term_offset, 'a, 'b) visitor_method
      method vtype : (typ, 'a, 'b) visitor_method
      method vvdec : (varinfo, 'a, 'b) visitor_method
      method vvrbl : (varinfo, 'a, 'b) visitor_method
    end

  type 'a inserting_visitor = { mk : 'b. (#frama_c_visitor as 'b) -> (#frama_c_inplace_inserting as 'a) }

  class proxy_frama_c_visitor : 'a inserting_visitor -> frama_c_visitor

  val inserting_statements : 'a inserting_visitor -> file -> unit

  type 'a attaching_visitor = { mk : 'b. attach:'b Do.attach -> (#frama_c_visitor as 'a) }

  val attaching_globs : 'a attaching_visitor -> file -> unit

  type 'a inserting_attaching_visitor =
    { mk : 'b 'c. attach:'b Do.attach -> (#frama_c_visitor as 'c) -> (#frama_c_inplace_inserting as 'a) }

  val inserting_statements_and_attaching_globs : 'a inserting_attaching_visitor -> file -> unit

  type 'a signal = 'a constraint 'a = < change : unit; .. >

  type 'a fixpoint_visitor = { mk : 'b. signal:'b signal -> (#frama_c_visitor as 'a) }

  val until_convergence : 'a fixpoint_visitor -> file -> unit
end

module Debug :
sig
  val check_exp_types : file -> unit
end

module Trie :
sig
  module type Map =
  sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

  module type S =
  sig
    type key
    type +'a t

    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : 'a t -> key list -> 'a -> 'a t
    val find_exn : 'a t -> key list -> 'a
    val find_all : 'a t -> key list -> 'a list
    val find_all2 : 'a t -> key list -> (key list * 'a) list
    val remove : 'a t -> key list -> 'a t
    val remove_all : 'a t -> key list -> 'a t
    val mem : 'a t -> key list -> bool
    val mem_any : 'a t -> key list -> bool
    val iter : (key list -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key list -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key list -> 'a -> 'b -> 'b) -> 'b -> 'a t -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

  module Make : functor (M : Map) -> S with type key = M.key
end

module StringTrie : Trie.S with type key = char
module Int64Trie : Trie.S with type key = int64
