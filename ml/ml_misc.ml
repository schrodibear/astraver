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

(******************************************************************************)

open Jc_ast
open Jc_env

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

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
