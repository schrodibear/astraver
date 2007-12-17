(* Interpretation of Ocaml types to Jessie *)

open Ml_misc
open Jc_env
open Jc_output
open Ml_ocaml.Types
open Ml_ocaml.Ident
open Ml_ocaml.Location
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

module ComparableCamlTypeList = struct
  type t = type_expr list
  let compare = Pervasives.compare (* maybe this should be changed *)
end

module ParamMap = Map.Make(ComparableCamlTypeList)

type ml_jessie_type =
  | MLTnot_closed
  | MLTnative of native_type
  | MLTrecord of Jc_env.struct_info * (string * ml_label_info) list
  | MLTvariant of Jc_env.struct_info * Jc_env.field_info *
      (string * ml_constructor_info) list

type ml_caml_type = {
  ml_ty_name: string;
  ml_ty_decl: Ml_ocaml.Types.type_declaration;
  mutable ml_ty_instances: ml_jessie_type ParamMap.t;
}

let ml_types = Hashtbl.create 11

let declare id td =
  let n = name id in
  Hashtbl.add ml_types n {
    ml_ty_name = n;
    ml_ty_decl = td;
    ml_ty_instances = ParamMap.empty;
  }

exception Not_closed

let rec make_type mlt =
  let not_implemented = not_implemented none in
  match mlt.desc with
    | Tvar -> raise Not_closed
    | Tarrow _ -> not_implemented "ml_type.ml: make_type: Tarrow"
    | Ttuple _ -> not_implemented "ml_type.ml: make_type: Ttuple"
    | Tconstr(path, args, _) ->
	begin match Ml_ocaml.Path.name path with
	  | "unit" -> MLTnative Tunit
	  | "int" -> MLTnative Tinteger
	  | "float" -> MLTnative Treal
	  | "bool" -> MLTnative Tboolean
	  | name ->
	      let ty = Hashtbl.find ml_types name in
	      begin try
		ParamMap.find args ty.ml_ty_instances
	      with Not_found ->
		try
		  let jcty = instance args ty in
		  ty.ml_ty_instances <-
		    ParamMap.add args jcty ty.ml_ty_instances;
		  jcty
		with Not_closed ->
		  MLTnot_closed
	      end
	end
    | Tobject _ -> not_implemented "ml_type.ml: make_type: Tobject"
    | Tfield _ -> not_implemented "ml_type.ml: make_type: Tfield"
    | Tnil -> not_implemented "ml_type.ml: make_type: Tnil"
    | Tlink t -> make_type t
    | Tsubst _ -> not_implemented "ml_type.ml: make_type: Tsubst"
    | Tvariant _ -> not_implemented "ml_type.ml: make_type: Tvariant"
    | Tunivar -> not_implemented "ml_type.ml: make_type: Tunivar"
    | Tpoly _ -> not_implemented "ml_type.ml: make_type: Tpoly"

and make mlt =
  match make_type mlt with
    | MLTnot_closed ->
	JCTlogic "caml_not_closed"
    | MLTnative t ->
	JCTnative t
    | MLTrecord(si, _)
    | MLTvariant(si, _, _) ->
	JCTpointer(si, Some(Num.num_of_int 0), Some(Num.num_of_int 0))

and instance args ty =
  log "Instanciate type %s with %d/%d arguments." ty.ml_ty_name
    (List.length args) ty.ml_ty_decl.type_arity;
  match ty.ml_ty_decl.type_kind with
    | Type_abstract ->
	not_implemented none "ml_type.ml: instance: Type_abstract"
    | Type_record(ll, _, _) ->
	let si = make_struct (fresh_ident ty.ml_ty_name) in
	let lbls = List.map
	  (fun (name, _, lty) ->
	     let app_ty = Ml_ocaml.Ctype.apply (Ml_ocaml.Env.empty)
	       ty.ml_ty_decl.type_params lty args in
	     let fi = make_field si name (make app_ty) in
	     let li = {
	       ml_li_name = name;
	       ml_li_structure = si;
	       ml_li_field = fi;
	     } in
	     name, li)
	  ll
	in
	MLTrecord(si, lbls)
    | Type_variant(cl, _) ->
	let si = make_struct (fresh_ident ty.ml_ty_name) in
	let tagfi = make_field si "jessica_tag" (JCTnative Tinteger) in
	let constrs = list_mapi
	  (fun tag (name, cargs) ->
	     let app_cargs = List.map
	       (fun caty ->
		  Ml_ocaml.Ctype.apply (Ml_ocaml.Env.empty)
		    ty.ml_ty_decl.type_params caty args)
	       cargs
	     in
	     let fi_args = list_mapi
	       (fun i ty -> make_field si (name^string_of_int i) (make ty))
	       app_cargs
	     in
	     let ci = {
	       ml_ci_name = name;
	       ml_ci_tag = tag;
	       ml_ci_structure = si;
	       ml_ci_tag_field = tagfi;
	       ml_ci_arguments = fi_args;
	     } in
	     name, ci)
	  cl
	in
	MLTvariant(si, tagfi, constrs)

let label recty ld =
  match make_type recty with
    | MLTrecord(_, lbls) -> List.assoc ld.lbl_name lbls
    | _ -> failwith "ml_type.ml: label: not a record type"

let constructor varty cd =
  match make_type varty with
    | MLTvariant(_, _, constrs) -> List.assoc cd.cstr_name constrs
    | _ -> failwith "ml_type.ml: constructor: not a variant type"

let jc_decl name = function
  | MLTnot_closed ->
      assert false
  | MLTnative t ->
      JClogic_type_def name
  | MLTrecord(si, lbls) ->
      JCstruct_def(
	si.jc_struct_info_name,
	(match si.jc_struct_info_parent with
	   | None -> None
	   | Some si -> Some si.jc_struct_info_name),
	List.map (fun (_, l) -> l.ml_li_field) lbls,
	[] (* TODO: invariants *)
      )
  | MLTvariant(si, tagfi, constrs) ->
      JCstruct_def(
	si.jc_struct_info_name,
	(match si.jc_struct_info_parent with
	   | None -> None
	   | Some si -> Some si.jc_struct_info_name),
	tagfi::
	  List.flatten (List.map (fun (_, l) -> l.ml_ci_arguments) constrs),
	[] (* TODO: invariants *)
      )

let jc_decls () =
  Hashtbl.fold
    (fun name ty acc ->
       ParamMap.fold
	 (fun _ ty acc ->
	    (jc_decl name ty)::acc)
	 ty.ml_ty_instances
	 acc)
    ml_types
    []

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
