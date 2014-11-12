open Cil_types
open Cil_datatype

open Format

module Emitters :
sig
  type t = Emitter.t
  val jessie : Emitter.t
end

exception Unsupported of string

module Console :
sig
  val fatal : ('a, formatter, unit, 'b) format4 -> 'a
  val unsupported : ('a, formatter, unit, 'b) format4 -> 'a
  val warning : ('a, formatter, unit) format -> 'a
  val general_warning : ('a, formatter, unit) format -> 'a
  val warn_once : string -> unit
  val debug : ('a, formatter, unit) format -> 'a
end

module List :
sig
  include module type of List
  val drop : int -> 'a list -> 'a list
  val take : int -> 'a list -> 'a list
  val range : int -> [< `Downto | `To ] -> int -> int list
end

module String :
sig
  include module type of String
  val explode : t -> char list
  val implode : char list -> t
  val filter_alphanumeric :
    assoc:(char * char) list -> default:char -> t -> t
end

module Tuple :
sig
  module T2 :
  sig
    type ('a, 'b) t = 'a * 'b
    val fdup2 : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
    val map1 : ('a -> 'b) -> 'a * 'c -> 'b * 'c
    val map2 : ('a -> 'b) -> 'c * 'a -> 'c * 'b
    val map : ('a -> 'b) -> 'a * 'a -> 'b * 'b
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

  val abort : 'a option
end

val ( |? ) : 'a option -> 'a -> 'a

module Location :
sig
  include module type of Location
  val is_unknown : Lexing.position * 'a -> bool
end

module Config :
sig
  include module type of Jessie_options
  val flatten_multi_dim_arrays : bool
end

module Framac :
sig
  module Ast = Ast
  module Type = Type
  module Vi = Cil_datatype.Varinfo
end

val mkStmt : ?ghost:bool -> Cil_types.stmtkind -> Cil_types.stmt

module Name :
sig
  module Of :
  sig
    module Attr :
    sig
      val embedded : string
      val noembed : string
      val padding : string
      val wrapper : string
      val arraylen : string
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
      val string_declspec : string
    end

    module Function :
    sig
      val assert_ : string
      val free : string
      val kfree : string
      val malloc : string
      val kmalloc : string
      val kzalloc : string
      val calloc : string
      val realloc : string
    end

    module File :
    sig
      val blockfuns_include : string
    end

    val typ : Cil_types.typ -> string
    val logic_type : Cil_types.logic_type -> string

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
  module Named :
  sig
    type 'a t = 'a Cil_types.named
    val mk : ?name:string list -> loc:Location.t -> 'a -> 'a t
  end

  module Exp :
  sig
    type t = Cil_types.exp
    val const : ?loc:Location.t -> Integer.t -> t
    val dummy_info : t -> t
  end

  module rec Vi :
  sig
    type var
    type func
    type 'a t = private Cil_types.varinfo

    module Function :
    sig
      type t = var Vi.t

      val of_varinfo : Cil_types.varinfo -> t option
      val of_varinfo_exn : Cil_types.varinfo -> t

      val is_assert : t -> bool
      val is_free : t -> bool
      val is_kfree : t -> bool
      val is_malloc : t -> bool
      val is_kmalloc : t -> bool
      val is_kzalloc : t -> bool
      val is_calloc : t -> bool
      val is_realloc : t -> bool
      val malloc : ?kernel:bool -> unit -> t
      val free : unit -> t
    end

    module Variable :
    sig
      type t = func Vi.t
      val of_varinfo : Cil_types.varinfo -> t option
      val of_varinfo_exn : Cil_types.varinfo -> t
    end
  end

  module Term :
  sig
    type t = Cil_types.term
    val is_base_addr : t -> bool
    val mk :
      ?name:string list ->
      typ:Cil_types.logic_type ->
      loc:Lexing.position * Lexing.position -> Cil_types.term_node -> t
    val of_var : Cil_types.varinfo -> t
    val typ_of_logic_c_type : Cil_types.logic_type -> Cil_types.typ
    module Env :
    sig
      type t
    end

    val to_exp_env : t -> Exp.t * Env.t
    val lval_to_lval_env : Cil_types.term_lval -> Cil_types.lval * Env.t
    val lhost_to_lhost_env : Cil_types.term_lhost -> Cil_types.lhost * Env.t
    val offset_to_offset_env : Cil_types.term_offset -> Cil_types.offset * Env.t
    val of_exp_env : Exp.t * Env.t -> t
    val offset_of_offset_env : Cil_types.offset * Env.t -> Cil_types.term_offset
    val lhost_of_lhost_env : Cil_types.lhost * Env.t -> Cil_types.term_lhost
    val lval_of_lval_env : Cil_types.lval * Env.t -> Cil_types.term_lval
    val of_exp : Exp.t -> t
    val offset_of_offset : Cil_types.offset -> Cil_types.term_offset
    val lhost_of_lhost : Cil_types.lhost -> Cil_types.term_lhost
    val lval_of_lval : Cil_types.lval -> Cil_types.term_lval
  end

  module Predicate :
  sig
    type t = Cil_types.predicate
    val of_exp_exn : Exp.t -> t Named.t
  end

  module Code_annot :
  sig
    type t =
      (Term.t, Predicate.t Named.t, Cil_types.identified_predicate,
       Cil_types.identified_term)
        Cil_types.code_annot
    val of_exp_exn : Exp.t -> Cil_types.code_annotation
  end

  module Offset :
  sig
    type t = Cil_types.offset
    val is_last : t -> bool
    val flatten : typ:Cil_types.typ -> t -> t
  end

  module Instr :
  sig
    type t = Cil_types.instr
    val alloc_singleton : lvar:Cil_types.varinfo -> typ:Cil_types.typ -> loc:Location.t -> t
    val alloc_array : lvar:Cil_types.varinfo -> typ:Cil_types.typ -> size:int64 -> loc:Location.t -> t
    val free : loc:Location.t -> Cil_types.varinfo -> t
  end

  module Stmt :
  sig
    type t = Cil_types.stmt
    val alloc_singleton : lvar:Cil_types.varinfo -> typ:Cil_types.typ -> loc:Location.t -> t
    val alloc_array : lvar:Cil_types.varinfo -> typ:Cil_types.typ -> size:int64 -> loc:Location.t -> t
    val free : loc:Location.t -> Cil_types.varinfo -> t
  end
end

module rec Type :
sig
  type composite
  type integral
  type ref
  type 'a t = private Cil_types.typ

  val almost_integer_type : Cil_types.typ
  val struct_type_for_void : Cil_types.typ
    module Logic_c_type :
    sig
      val map_default :
        default:'a -> (Cil_types.typ -> 'a) -> Cil_types.logic_type -> 'a
      val map : (Cil_types.typ -> 'a) -> Cil_types.logic_type -> 'a
    end

    module Ref :
    sig
      type t = ref Type.t
      val singleton : msg:'a -> Cil_types.typ -> t
      val array : Cil_types.typ * Cil_types.exp * Cil_types.attributes -> t
      val size : t -> int64
      val is_ref : Cil_types.typ -> bool
      val is_array_ref : Cil_types.typ -> bool
      val of_array_exn : Cil_types.typ -> t
    end

    module rec Composite :
    sig
      type t = composite Type.t

      val of_typ : Cil_types.typ -> t option
      val of_typ_exn : Cil_types.typ -> t
      val unique_field_exn : t -> Cil_types.fieldinfo
      val compinfo_cname : t -> string
      val compinfo : t -> Cil_types.compinfo

      module Ci :
      sig
        type t = compinfo

        module Struct :
        sig
          type t = compinfo

          val empty : string -> Cil_types.compinfo
          val singleton : ?padding:int -> string -> string -> Cil_types.typ -> Cil_types.compinfo
        end

        val size : Cil_types.compinfo -> int option
        val padding_field : ?fsize_in_bits:int -> Cil_types.compinfo -> Cil_types.fieldinfo
        val fix_size : ?original_size:int -> Cil_types.compinfo -> unit
        val proper_fields : Cil_types.compinfo -> Cil_types.fieldinfo list
      end
    end

    val promote_argument_type : Cil_types.typ -> Cil_types.typ
    val size_in_bits_exn : Cil_types.typ -> int64

    module Integral :
    sig
      type t = integral Type.t

      val of_typ : Cil_types.typ -> t option
      val of_typ_exn : Cil_types.typ -> t

      module IKind :
      sig
        type t = ikind
        val size_in_bytes : Cil_types.ikind -> int
      end

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
  val retaining_size_of_composite : Cil_types.compinfo -> (Cil_types.compinfo -> 'a) -> 'a

  type 'a attach = 'a
    constraint 'a =
      < globaction : (unit -> unit) -> unit;
      global : Cil_types.global -> unit; .. >

  type attaching_action = { perform : 'a. attach:'a attach -> Cil_types.file -> unit }

  val attaching_globs : attaching_action -> Cil_types.file -> unit

  val on_term_offset :
    ?pre:(Cil_types.offset -> Cil_types.offset) ->
    ?post:(Cil_types.offset -> Cil_types.offset) ->
    Cil_types.term_offset -> Cil_types.term_offset Cil.visitAction

  val on_term_lval :
    ?pre:(Cil_types.lval -> Cil_types.lval) ->
    ?post:(Cil_types.lval -> Cil_types.lval) ->
    Cil_types.term_lval -> Cil_types.term_lval Cil.visitAction

  val on_term :
    ?pre:(Cil_types.exp -> Cil_types.exp) ->
    ?post:(Cil_types.exp -> Cil_types.exp) ->
    Cil_types.term -> Cil_types.term Cil.visitAction
end

module Visit :
sig
  type insert

  val prepending : Cil_types.stmt list -> insert
  val appending : Cil_types.stmt list -> insert
  val inserting : before:Cil_types.stmt list -> after:Cil_types.stmt list -> insert

  val inserting_nothing : insert

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
  end

  type ('a, 'result, 'visit_action) context =
    | Local : ('a, 'a * insert, 'a Local.visit_action) context
    | Global : ('a, 'a, 'a Cil.visitAction) context

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
  end

  val wrap : ('a, 'b, 'c) context -> 'a Cil.visitAction -> 'c

  type ('a, 'r, 'v) visitor_method = ('a, 'r, 'v) context -> 'a -> 'v

  class frama_c_inplace_inserting :
    object
      val super : Visitor.frama_c_inplace
      method behavior : Cil.visitor_behavior
      method current_func : Cil_types.fundec option
      method current_kf : Cil_types.kernel_function option
      method current_kinstr : Cil_types.kinstr
      method current_stmt : Cil_types.stmt option
      method fill_global_tables : unit
      method frama_c_plain_copy : Visitor.frama_c_visitor
      method get_filling_actions : (unit -> unit) Queue.t
      method plain_copy_visitor : Cil.cilVisitor
      method pop_stmt : Cil_types.stmt -> unit
      method project : Project_skeleton.t option
      method push_stmt : Cil_types.stmt -> unit
      method queueInstr : Cil_types.instr list -> unit
      method reset_current_func : unit -> unit
      method reset_current_kf : unit -> unit
      method set_current_func : Cil_types.fundec -> unit
      method set_current_kf : Cil_types.kernel_function -> unit
      method unqueueInstr : unit -> Cil_types.instr list
      method vallocates :
          (Cil_types.identified_term list, 'a, 'b) visitor_method
      method vallocation :
        (Cil_types.identified_term Cil_types.allocation, 'a, 'b)
          visitor_method
      method vannotation :
        Cil_types.global_annotation ->
        Cil_types.global_annotation Cil.visitAction
      method vassigns :
        (Cil_types.identified_term Cil_types.assigns, 'a, 'b)
          visitor_method
      method vattr :
        (Cil_types.attribute list, 'a, 'b) context ->
        Cil_types.attribute list -> 'b
      method vattrparam : (Cil_types.attrparam, 'a, 'b) visitor_method
      method vbehavior : (Cil_types.funbehavior, 'a, 'b) visitor_method
      method vblock : Cil_types.block -> Cil_types.block Local.visit_action
      method vcode_annot :
          Cil_types.code_annotation ->
          Cil_types.code_annotation Local.visit_action
      method vcompinfo :
        Cil_types.compinfo -> Cil_types.compinfo Cil.visitAction
      method vdeps :
        (Cil_types.identified_term Cil_types.deps, 'a, 'b) visitor_method
      method venuminfo :
        Cil_types.enuminfo -> Cil_types.enuminfo Cil.visitAction
      method venumitem :
        Cil_types.enumitem -> Cil_types.enumitem Cil.visitAction
      method vexpr : (Cil_types.exp, 'a, 'b) visitor_method
      method vfieldinfo :
        Cil_types.fieldinfo -> Cil_types.fieldinfo Cil.visitAction
      method vfile : Cil_types.file -> Cil_types.file Cil.visitAction
      method vfrees :
        (Cil_types.identified_term list, 'a, 'b) visitor_method
      method vfrom :
        (Cil_types.identified_term Cil_types.from, 'a, 'b) visitor_method
      method vfunc :
        Cil_types.fundec -> Cil_types.fundec Fundec.visit_action
      method vglob :
        Cil_types.global -> Cil_types.global list Cil.visitAction
      method vglob_aux :
        Cil_types.global -> Cil_types.global list Cil.visitAction
      method videntified_predicate :
        (Cil_types.identified_predicate, 'a, 'b) visitor_method
      method videntified_term :
        (Cil_types.identified_term, 'a, 'b) visitor_method
      method vimpact_pragma :
        (Cil_types.term Cil_types.impact_pragma, 'a, 'b) visitor_method
      method vinit :
        (Cil_types.init, 'a, 'b) context ->
        Cil_types.varinfo -> Cil_types.offset -> Cil_types.init -> 'b
      method vinitoffs : (Cil_types.offset, 'a, 'b) visitor_method
      method vinst :
        Cil_types.instr -> Cil_types.instr list Local.visit_action
      method vjessie_pragma :
        Cil_types.term Cil_types.jessie_pragma ->
        Cil_types.term Cil_types.jessie_pragma Local.visit_action
      method vlogic_ctor_info_decl :
        Cil_types.logic_ctor_info ->
        Cil_types.logic_ctor_info Cil.visitAction
      method vlogic_ctor_info_use :
        (Cil_types.logic_ctor_info, 'a, 'b) visitor_method
      method vlogic_info_decl :
        Cil_types.logic_info -> Cil_types.logic_info Cil.visitAction
      method vlogic_info_use :
        (Cil_types.logic_info, 'a, 'b) visitor_method
      method vlogic_label : (Cil_types.logic_label, 'a, 'b) visitor_method
      method vlogic_type : (Cil_types.logic_type, 'a, 'b) visitor_method
      method vlogic_type_def :
        Cil_types.logic_type_def ->
        Cil_types.logic_type_def Cil.visitAction
      method vlogic_type_info_decl :
        Cil_types.logic_type_info ->
        Cil_types.logic_type_info Cil.visitAction
      method vlogic_type_info_use :
        (Cil_types.logic_type_info, 'a, 'b) visitor_method
      method vlogic_var_decl : (Cil_types.logic_var, 'a, 'b) visitor_method
      method vlogic_var_use : (Cil_types.logic_var, 'a, 'b) visitor_method
      method vloop_pragma :
        Cil_types.term Cil_types.loop_pragma ->
        Cil_types.term Cil_types.loop_pragma Local.visit_action
      method vlval : (Cil_types.lval, 'a, 'b) visitor_method
      method vmodel_info :
        Cil_types.model_info -> Cil_types.model_info Cil.visitAction
      method voffs : (Cil_types.offset, 'a, 'b) visitor_method
      method vpredicate : (Cil_types.predicate, 'a, 'b) visitor_method
      method vpredicate_named :
        (Cil_types.predicate Cil_types.named, 'a, 'b) visitor_method
      method vquantifiers : (Cil_types.quantifiers, 'a, 'b) visitor_method
      method vslice_pragma :
        (Cil_types.term Cil_types.slice_pragma, 'a, 'b) visitor_method
      method vspec : (Cil_types.funspec, 'a, 'b) visitor_method
      method vstmt : Cil_types.stmt -> Cil_types.stmt Local.visit_action
      method vstmt_aux :
        Cil_types.stmt -> Cil_types.stmt Local.visit_action
      method vterm : (Cil_types.term, 'a, 'b) visitor_method
      method vterm_lhost : (Cil_types.term_lhost, 'a, 'b) visitor_method
      method vterm_lval : (Cil_types.term_lval, 'a, 'b) visitor_method
      method vterm_node : (Cil_types.term_node, 'a, 'b) visitor_method
      method vterm_offset : (Cil_types.term_offset, 'a, 'b) visitor_method
      method vtype : (Cil_types.typ, 'a, 'b) visitor_method
      method vvdec : (Cil_types.varinfo, 'a, 'b) visitor_method
      method vvrbl : (Cil_types.varinfo, 'a, 'b) visitor_method
    end

  class proxy_frama_c_visitor : #frama_c_inplace_inserting -> Visitor.frama_c_visitor

  type attaching_visitor = {  mk : 'a. attach:'a Do.attach -> Visitor.frama_c_visitor }

  val attaching_globs : attaching_visitor -> Cil_types.file -> unit

  val inserting_statements : #frama_c_inplace_inserting -> file -> unit

  type 'a signal = 'a constraint 'a = < change : unit; .. >

  type fixpoint_visitor = { mk : 'a. signal:'a signal -> Visitor.frama_c_visitor }

  val until_convergence : fixpoint_visitor -> Cil_types.file -> unit
end

module Debug :
sig
  val check_exp_types : Cil_types.file -> unit
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

module StringTrie : Trie.S with type key := char
module Int64Trie : Trie.S with type key := int64
