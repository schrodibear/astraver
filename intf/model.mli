

(** {2 columns of the model} *)

val name : string GTree.column
val stat : string GTree.column
val fullname : string GTree.column
val result : int GTree.column
val parent : string GTree.column
val total : int GTree.column

(** {2 prover data} *)

type prover = {
  pr_id : DpConfig.prover_id;
  pr_info : DpConfig.prover_data;
  pr_result : int GTree.column;
  pr_icon : GtkStock.id GTree.column;
  mutable pr_viewcol : GTree.view_column option;
  pr_enc : Options.encoding;
}
    (** type of a prover description in the model *)

val ergo : prover
val simplify : prover
val z3SS : prover
val yicesSS : prover
val cvc3SS : prover
val gappa: prover

val prover_id : prover -> string
  (** return a prover identifier with name and encoding, e.g. "Z3(SS)",
      which can be used for indexing *)

val prover_name_with_version_and_enc : prover -> string
  (** return a printable prover name under the form "prover_id\nversion\n(encoding)" *)

(** {2 provers with their current selected/deselected status *)

val get_prover_states : unit -> (prover*bool) list
  (** returns the list of known provers 
      with there current state: selected or not *)

val select_prover : prover -> unit
  (* sets prover state to selected *)

val deselect_prover : prover -> unit
  (* sets prover state to deselected *)

val get_prover : string -> prover
  (** search for an existing prover from its unique id (see [prover_id]
      above). raises Not_found if no prover of this id exist *)

val get_default_prover : unit -> prover

val set_default_prover : prover -> unit

(** {3 not documented} *)

val fq : string Queue.t
(* queue of functions in the model *)

val create_model : unit -> GTree.tree_store

val frows : (string, Gtk.tree_iter) Hashtbl.t
val fwrows : (string, (prover, string) Hashtbl.t) Hashtbl.t
val first_row : Gtk.tree_iter option ref



val find_fct : string -> Gtk.tree_iter

val iter_fobligs : string -> (Gtk.tree_iter -> unit) -> unit

val orows : (string, Gtk.tree_iter) Hashtbl.t
  
val add_failure : string -> prover -> string -> unit


val find_oblig : 
  string -> Loc.floc * Logic_decl.vc_expl * string * Cc.sequent Env.scheme
val find_fobligs : string -> Gtk.tree_iter Queue.t
val obligs :
  (string, Loc.floc * Logic_decl.vc_expl * string * Cc.sequent Env.scheme)
  Hashtbl.t




