

type goal = private {
  goal_expl : Logic_decl.vc_expl;
  goal_file : string;
}

type lemma = private {
  lemma_name : string;
  lemma_loc : Loc.floc;
  lemma_goal : goal;
}

type behavior = {
  behavior_name : string;
  mutable behavior_goals : goal list;
}

type funct = private {
  function_name : string;
  function_loc : Loc.floc;
  mutable function_behaviors : behavior list;
  mutable function_visible : bool;
}
  

type t = private {
  project_name : string;
  mutable project_context_file : string;
  mutable project_lemmas : lemma list;
  mutable project_functions : funct list;
}

(* creations *)
val create : string -> t
val set_project_context_file : t -> string -> unit
val add_lemma : t -> string -> Logic_decl.vc_expl -> string -> lemma
val add_function : t -> string -> Loc.floc -> funct
val add_behavior : funct -> string -> behavior
val add_goal : behavior -> Logic_decl.vc_expl -> string -> goal

(* toggle visibility *)

val toggle_lemma : lemma -> unit
val toggle_function : funct -> unit

(* save/load *)

val save : t -> string -> unit

val load : string -> t
