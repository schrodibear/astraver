

open Java_env
open Java_ast

let expr_no_loc e = 
  { java_pexpr_loc = Loc.dummy_position ; java_pexpr_node = e }

let expr_node_true = JPElit(Bool true)

let expr_true = expr_no_loc expr_node_true

let expr_zero = expr_no_loc (JPElit(Integer "0"))

(*
let default_loop_annotation =
  { kml_loop_invariant = expr_true;
    kml_loop_assigns = None;
    kml_loop_variant = expr_zero;
  }

let default_method_specification =
  { kml_requires = expr_true;
  }
*)

open Java_env

let null_type = JTYbase Tnull
let unit_type = JTYbase Tunit
let boolean_type = JTYbase Tboolean
let integer_type = JTYbase Tinteger
let real_type = JTYbase Treal

let logic_fun_tag_counter = ref 0

let make_term_op name ty =
  incr logic_fun_tag_counter;
  { java_logic_info_tag = !logic_fun_tag_counter;
    java_logic_info_name = name;
    java_logic_info_result_type = Some ty;
    java_logic_info_parameters = [];
(*
    java_logic_info_effects = empty_effects;
*)
    java_logic_info_calls = [];
  }

let add_int = make_term_op "add_int" integer_type
let mul_int = make_term_op "mul_int" integer_type

let make_pred_op name =
  incr logic_fun_tag_counter;
  { java_logic_info_tag = !logic_fun_tag_counter;
    java_logic_info_name = name;
    java_logic_info_result_type = None;
    java_logic_info_parameters = [];
(*
    java_logic_info_effects = empty_effects;
*)
    java_logic_info_calls = [];
  }

let eq_int = make_pred_op "eq_int"
let ge_int = make_pred_op "ge_int"
let gt_int = make_pred_op "gt_int"
let lt_int = make_pred_op "lt_int"
let le_int = make_pred_op "le_int"
let ne_int = make_pred_op "ne_int"


(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
