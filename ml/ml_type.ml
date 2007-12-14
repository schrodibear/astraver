(* Interpretation of Ocaml types to Jessie *)

open Ml_misc
open Jc_env
open Ml_ocaml.Types
open Format

let rec print_type fmt t =
  fprintf fmt "(level %d, id %d: " t.level t.id;
  begin match t.desc with
    | Tvar ->
	fprintf fmt "Tvar"
    | Tarrow(_, a, b, _) ->
	print_type fmt a;
	fprintf fmt " -> ";
	print_type fmt b
    | Ttuple tl ->
	List.iter (fun t -> print_type fmt t; fprintf fmt " * ") tl
    | Tconstr(path, tl, _) ->
	fprintf fmt "Tconstr %s [ " (Ml_ocaml.Path.name path);
	List.iter (fun t -> print_type fmt t; fprintf fmt "; ") tl;
	fprintf fmt "]";
    | Tobject _ ->
	fprintf fmt "Tobject"
    | Tfield _ ->
	fprintf fmt "Tfield"
    | Tnil ->
	fprintf fmt "Tnil"
    | Tlink lt ->
	fprintf fmt "Tlink";
	print_type fmt lt
    | Tsubst _ ->
	fprintf fmt "Tsubst"
    | Tvariant _ ->
	fprintf fmt "Tvariant"
    | Tunivar ->
	fprintf fmt "Tunivar"
    | Tpoly _ ->
	fprintf fmt "Tpoly"
  end;
  fprintf fmt ")"

let print_type t =
  let fmt = formatter_of_out_channel stdout in
  print_type fmt t;
  fprintf fmt "@."

type ml_label_info = {
  ml_li_name: string;
  ml_li_structure: Jc_env.struct_info;
  ml_li_field: Jc_env.field_info;
}

type ml_constructor_info = {
  ml_ci_name: string;
  ml_ci_tag: int;
  ml_ci_structure: Jc_env.struct_info;
  ml_ci_tag_field: Jc_env.field_info;
  ml_ci_arguments: Jc_env.field_info list;
}

let declare id td =
  log "Type declaration parameters:";
  List.iter (fun t -> print_type t) td.type_params;
  match td.type_kind with
    | Type_abstract -> log "Type_abstract"
    | Type_variant(cl, _) ->
	List.iter
	  (fun (n, args) ->
	     log "Constructor %s:" n;
	     List.iter print_type args) cl
    | Type_record(fl, _, _) ->
	List.iter
	  (fun (n, _, t) ->
	     log "Label %s:" n;
	     print_type t) fl

let make mlt = assert false

let label ld = assert false

let constructor cd = assert false

let jc_decls () = assert false

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
