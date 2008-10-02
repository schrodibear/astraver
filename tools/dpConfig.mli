


type prover =
  {
    name : string;
    mutable version: string;
    version_switch : string;
    version_regexp : string;
    mutable command : string;
    command_switches : string;
(*
    correct_exit_codes : int list;
*)
    valid_regexp : string;
    mutable valid_cregexp : Str.regexp option;
    undecided_regexp : string;
    mutable undecided_cregexp : Str.regexp option;
(*
    invalid_regexp : string;
    invalid_cregexp : Str.regexp option;
*)
  }
    

val alt_ergo : prover

val simplify : prover

val z3 : prover

val yices : prover

val cvc3 : prover

val prover_list : (prover * string list) list

val load_rc_file : unit -> unit

val save_rc_file : unit -> unit
