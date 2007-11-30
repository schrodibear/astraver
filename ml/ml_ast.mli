(* Abstract syntax tree *)

open Ml_ocaml
open Asttypes
open Misc
open Types

(* Value expressions for the core language *)

type pattern =
  { jpat_desc: pattern_desc;
    jpat_loc: Location.t;
    jpat_type: type_expr;
    jpat_env: Env.t }

and pattern_desc =
    JTpat_any
  | JTpat_var of Ident.t
  | JTpat_alias of pattern * Ident.t
  | JTpat_constant of constant
  | JTpat_tuple of pattern list
  | JTpat_construct of constructor_description * pattern list
  | JTpat_variant of label * pattern option * row_desc
  | JTpat_record of (label_description * pattern) list
  | JTpat_array of pattern list
  | JTpat_or of pattern * pattern * Path.t option

type partial = Typedtree.partial
type optional = Typedtree.optional

type expression =
  { jexp_desc: expression_desc;
    jexp_loc: Location.t;
    jexp_type: type_expr;
    jexp_env: Env.t }

and expression_desc =
    JTexp_ident of Path.t * value_description
  | JTexp_constant of constant
  | JTexp_let of rec_flag * (pattern * expression) list * expression
  | JTexp_function of (pattern * expression) list * partial
  | JTexp_apply of expression * (expression option * optional) list
  | JTexp_match of expression * (pattern * expression) list * partial
  | JTexp_try of expression * (pattern * expression) list
  | JTexp_tuple of expression list
  | JTexp_construct of constructor_description * expression list
  | JTexp_variant of label * expression option
  | JTexp_record of (label_description * expression) list * expression option
  | JTexp_field of expression * label_description
  | JTexp_setfield of expression * label_description * expression
  | JTexp_array of expression list
  | JTexp_ifthenelse of expression * expression * expression option
  | JTexp_sequence of expression * expression
  | JTexp_while of expression * expression
  | JTexp_for of
      Ident.t * expression * expression * direction_flag * expression
  | JTexp_when of expression * expression
(*  | JTexp_send of expression * meth
  | JTexp_new of Path.t * class_declaration*)
  | JTexp_instvar of Path.t * Path.t
  | JTexp_setinstvar of Path.t * Path.t * expression
  | JTexp_override of Path.t * (Path.t * expression) list
(*  | JTexp_letmodule of Ident.t * module_expr * expression*)
  | JTexp_assert of expression
  | JTexp_assertfalse
  | JTexp_lazy of expression
(*  | JTexp_object of class_structure * class_signature * string list*)

type structure = structure_item list

and structure_item =
    JTstr_eval of expression
  | JTstr_value of rec_flag * (pattern * expression) list
(*  | JTstr_primitive of Ident.t * value_description*)
  | JTstr_type of (Ident.t * type_declaration) list
(*  | JTstr_exception of Ident.t * exception_declaration
  | JTstr_exn_rebind of Ident.t * Path.t
  | JTstr_module of Ident.t * module_expr
  | JTstr_recmodule of (Ident.t * module_expr) list
  | JTstr_modtype of Ident.t * module_type
  | JTstr_open of Path.t
  | JTstr_class of
      (Ident.t * int * string list * class_expr * virtual_flag) list
  | JTstr_cltype of (Ident.t * cltype_declaration) list
  | JTstr_include of module_expr * Ident.t list*)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessica.byte"
End: 
*)
