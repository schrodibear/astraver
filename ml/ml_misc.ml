open Lexing
open Ml_ocaml.Location

module StringMap = Map.Make(String)

(******************************************************************************)

let error x =
  Printf.ksprintf
    (fun s -> Printf.fprintf stderr "%s\n%!" s; exit 1) x

let locate_error loc =
  Printf.ksprintf
    (fun s -> error "File \"%s\", line %d, characters %d-%d:\n%s"
       loc.loc_start.pos_fname
       loc.loc_start.pos_lnum
       (loc.loc_start.pos_cnum - loc.loc_start.pos_bol)
       (loc.loc_end.pos_cnum - loc.loc_start.pos_bol)
       s)

let caml_error loc report error =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  report fmt error;
  Format.pp_print_flush fmt ();
  locate_error loc "%s" (Buffer.contents buf)

let log x =
  Printf.ksprintf
    (fun s -> Printf.printf "%s\n%!" s) x

let not_implemented loc =
  Printf.ksprintf (locate_error loc "Not implemented (%s)")

let fresh_int = let c = ref(-1) in fun () -> incr c; !c

let rec list_filter_option acc = function
  | [] -> List.rev acc
  | None::rem -> list_filter_option acc rem
  | (Some x)::rem -> list_filter_option (x::acc) rem
let list_filter_option l = list_filter_option [] l

let rec list_fold_map acc f useracc = function
  | [] -> useracc, List.rev acc
  | x::rem ->
      let useracc', y = f useracc x in
      list_fold_map (y::acc) f useracc' rem
let list_fold_map x = list_fold_map [] x

(******************************************************************************)

open Jc_ast
open Jc_env

let is_unit t = t = JCTnative Tunit

let is_void_statement_node = function
  | JCTSblock []
  | JCTSexpr({ jc_texpr_node = JCTEconst JCCvoid }) -> true
  | _ -> false

let is_void_statement s = is_void_statement_node s.jc_tstatement_node

let make_expr ?(loc=Loc.dummy_position) ?(label="") ~node ~ty = {
  jc_texpr_node = node;
  jc_texpr_loc = loc;
  jc_texpr_type = ty;
  jc_texpr_label = label; (* ? *)
}

let make_assertion ?(loc=Loc.dummy_position) ?(label="") ~node = {
  jc_assertion_node = node;
  jc_assertion_loc = loc;
  jc_assertion_label = label; (* ? *)
}

let make_term ?(loc=Loc.dummy_position) ?(label="") ~node ~ty = {
  jc_term_node = node;
  jc_term_type = ty;
  jc_term_loc = loc;
  jc_term_label = label;
}

let make_bool_expr ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_expr ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tboolean)

let make_int_expr ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_expr ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tinteger)

let make_and a b = match a.jc_assertion_node, b.jc_assertion_node with
  | JCAand al, JCAand bl -> make_assertion (JCAand(al@bl))
  | JCAtrue, _ -> b
  | _, JCAtrue -> a
  | _ -> make_assertion (JCAand [ a; b ])

let make_and_list = List.fold_left make_and (make_assertion JCAtrue)

let make_pointer_type si =
  JCTpointer(si, Some (Num.num_of_int 0), Some (Num.num_of_int 0))

let expr_of_int i = make_int_expr(JCTEconst(JCCinteger(string_of_int i)))

(* Jc_pervasives produces names that will be used by Jessie too, which is bad *)
let new_var = let var_cnt = ref 0 in fun ty ->
  incr var_cnt;
  let id = "jessica_"^(string_of_int !var_cnt) in
  {
    jc_var_info_tag = fresh_int ();
    jc_var_info_name = id;
    jc_var_info_final_name = id;
    jc_var_info_type = ty;
    jc_var_info_formal = false;
    jc_var_info_assigned = false;
    jc_var_info_static = false;
  }

let ignored_var ty = {
  jc_var_info_tag = fresh_int ();
  jc_var_info_name = "jessica_ignored";
  jc_var_info_final_name = "jessica_ignored";
  jc_var_info_type = ty;
  jc_var_info_formal = false;
  jc_var_info_assigned = false;
  jc_var_info_static = false;
}

let expr_seq_to_let =
  List.fold_right
    (fun e acc ->
       make_expr
	 (JCTElet(ignored_var e.jc_texpr_type, e, acc))
	 acc.jc_texpr_type)

let make_statement ?(loc=Loc.dummy_position) s = {
  jc_tstatement_node = s;
  jc_tstatement_loc = loc;
}

let make_statement_block ?(loc=Loc.dummy_position) sl =
  match List.filter (fun s -> not (is_void_statement s)) sl with
    | ([] as l)
    | ([ { jc_tstatement_node = JCTSdecl _ } ] as l)
    | (_::_::_ as l) -> make_statement ~loc:loc (JCTSblock l)
    | [ x ] -> x

let make_affect vi e =
  if is_unit e.jc_texpr_type then
    (log "affect unit: %s" vi.jc_var_info_name; make_statement (JCTSexpr e))
  else
    (log "affect not unit: %s" vi.jc_var_info_name; make_statement (JCTSexpr({ e with jc_texpr_node = JCTEassign_var(vi, e) })))

let make_discard e =
  make_statement (JCTSexpr e)

let make_return e =
  make_statement (JCTSreturn(e.jc_texpr_type, e))

let make_var_decl vi init s =
  make_statement (JCTSdecl(vi, init, s))

let void = make_expr (JCTEconst JCCvoid) (JCTnative Tunit)

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
