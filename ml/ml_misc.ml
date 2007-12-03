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

let make_bool_expr ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_expr ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tboolean)

let make_int_expr ?(loc=Loc.dummy_position) ?(label="") ~node =
  make_expr ~loc:loc ~label:label ~node:node ~ty:(JCTnative Tinteger)

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
