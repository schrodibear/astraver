

type prover = {
  pr_id : DpConfig.prover_id;
  pr_info : DpConfig.prover_data;
  pr_result : int GTree.column;
  pr_icon : GtkStock.id GTree.column;
  mutable pr_viewcol : GTree.view_column option;
  pr_enc : Options.encoding;
}

val all_known_provers : prover list

val name : string GTree.column
val stat : string GTree.column
val fullname : string GTree.column
val result : int GTree.column
val parent : string GTree.column
val total : int GTree.column
val fq : string Queue.t

val create_model : unit -> GTree.tree_store

val frows : (string, Gtk.tree_iter) Hashtbl.t
val fwrows : (string, (prover, string) Hashtbl.t) Hashtbl.t
val first_row : Gtk.tree_iter option ref

val select_prover : prover -> unit
val deselect_prover : prover -> unit


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


val prover_name_with_version_and_enc : prover -> string


val prover_id : prover -> string

val get_default_prover : unit -> prover

val get_provers : unit -> prover list

val get_provers_s : unit -> prover list

val add_all_provers : unit -> unit

val add_provers : string list -> unit

val set_prover : prover -> unit

exception No_such_prover

val get_prover : string -> prover

