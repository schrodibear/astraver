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

let rec list_fold_mapi i acc f useracc = function
  | [] -> useracc, List.rev acc
  | x::rem ->
      let useracc', y = f useracc i x in
      list_fold_mapi (i+1) (y::acc) f useracc' rem
let list_fold_mapi x = list_fold_mapi 0 [] x

let rec list_mapi f index acc = function
  | [] -> List.rev acc
  | x::rem -> list_mapi f (index + 1) ((f index x)::acc) rem
let list_mapi f = list_mapi f 0 []

let rec list_iteri f index = function
  | [] -> ()
  | x::rem ->
      f index x;
      list_iteri f (index + 1) rem
let list_iteri f = list_iteri f 0

(******************************************************************************)

let identifier_of_symbol_char = function
  | '!' -> "bang"
  | ':' -> "colon"
  | '=' -> "equal"
  | c -> String.make 1 c

let identifier_of_symbol = function
  | "ref" -> "jessica_ref"
  | s ->
      let buf = Buffer.create 10 in
      for i = 0 to String.length s - 1 do
	Buffer.add_string buf (identifier_of_symbol_char s.[i])
      done;
      Buffer.contents buf

let idents = Hashtbl.create 111 (* 111 = 42 + 69 *)

let fresh_ident base =
  if Hashtbl.mem idents base then begin
    let i = Hashtbl.find idents base + 1 in
    Hashtbl.replace idents base i;
    identifier_of_symbol base ^ string_of_int i
  end else begin
    Hashtbl.add idents base 0;
    identifier_of_symbol base
  end

(******************************************************************************)

open Jc_ast
open Jc_env
open Jc_output

let default_region = {
  jc_reg_variable = false;
  jc_reg_id = 0;
  jc_reg_name = "jessica_region";
}

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
  jc_texpr_region = default_region;
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
  jc_term_region = default_region;
}

let make_bool_expr ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_expr ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tboolean)

let make_int_expr ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_expr ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tinteger)

let make_bool_term ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_term ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tboolean)

let make_int_term ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_term ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tinteger)

let make_eq_term a b =
  (* it shouldn't always be "int"... but for the output it works *)
  make_bool_term (JCTbinary(a, Beq_int, b))

let make_eq_assertion a b =
  make_assertion (JCAbool_term(make_eq_term a b))

let make_var_term vi =
  make_term (JCTvar vi) vi.jc_var_info_type

let make_and a b = match a.jc_assertion_node, b.jc_assertion_node with
  | JCAand al, JCAand bl -> make_assertion (JCAand(al@bl))
  | JCAtrue, _ -> b
  | _, JCAtrue -> a
  | _ -> make_assertion (JCAand [ a; b ])

let make_or a b = match a.jc_assertion_node, b.jc_assertion_node with
  | JCAor al, JCAor bl -> make_assertion (JCAor(al@bl))
  | JCAfalse, _ -> b
  | _, JCAfalse -> a
  | _ -> make_assertion (JCAor [ a; b ])

let make_and_list = List.fold_left make_and (make_assertion JCAtrue)

let make_or_list = List.fold_left make_or (make_assertion JCAfalse)

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
    jc_var_info_region = default_region;
  }

let ignored_var ty = {
  jc_var_info_tag = fresh_int ();
  jc_var_info_name = "jessica_ignored";
  jc_var_info_final_name = "jessica_ignored";
  jc_var_info_type = ty;
  jc_var_info_formal = false;
  jc_var_info_assigned = false;
  jc_var_info_static = false;
  jc_var_info_region = default_region;
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
  (* remove voids and flatten blocks *)
  let sl = List.map
    (fun s ->
       if is_void_statement s then [] else
	 match s with
	   | { jc_tstatement_node = JCTSblock l } -> l
	   | _ -> [ s ])
    sl
  in
  match List.flatten sl with
    | ([] as l)
    | ([ { jc_tstatement_node = JCTSdecl _ } ] as l)
    | (_::_::_ as l) -> make_statement ~loc:loc (JCTSblock l)
    | [ x ] -> x

let make_affect vi e =
  if is_unit e.jc_texpr_type then
    make_statement (JCTSexpr e)
  else
    make_statement (JCTSexpr({ e with jc_texpr_node = JCTEassign_var(vi, e) }))

let make_affect_field x fi e =
  if is_unit e.jc_texpr_type then
    make_statement (JCTSexpr e)
  else
    make_statement (JCTSexpr({ e with jc_texpr_node =
				 JCTEassign_heap(x, fi, e) }))

let make_discard e =
  make_statement (JCTSexpr e)

let make_return e =
  make_statement (JCTSreturn(e.jc_texpr_type, e))

let make_var_decl vi init s =
  make_statement (JCTSdecl(vi, init, s))

let make_alloc_tmp si cont =
  let tmp_ty = make_pointer_type si in
  let tmp_var = new_var tmp_ty in
  let tmp_expr = make_expr (JCTEvar tmp_var) tmp_ty in
  let tmp_init = make_expr (JCTEalloc(expr_of_int 1, si)) tmp_ty in
  make_var_decl tmp_var (Some tmp_init) (cont tmp_var tmp_expr)

let void = make_expr (JCTEconst JCCvoid) (JCTnative Tunit)

let make_struct name = {
  jc_struct_info_name = name;
  jc_struct_info_parent = None;
  jc_struct_info_root = name;
  jc_struct_info_fields = [];
}

let make_field si name jcty =
  let fi = {
    jc_field_info_tag = fresh_int ();
    jc_field_info_name = name;
    jc_field_info_final_name = name;
    jc_field_info_type = jcty;
    jc_field_info_struct = si;
    jc_field_info_root = si.jc_struct_info_root;
    jc_field_info_rep = false;
  } in
  si.jc_struct_info_fields <- fi::si.jc_struct_info_fields;
  fi

let dummy_struct = make_struct "dummy_struct"

let make_struct_def si invs =
  JCstruct_def(
    si.jc_struct_info_name,
    (match si.jc_struct_info_parent with
       | None -> None
       | Some si -> Some si.jc_struct_info_name),
    si.jc_struct_info_fields,
    invs
  )

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
