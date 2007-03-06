

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
