(* Interpretation of Ocaml types to Jessie *)

open Ml_misc
open Jc_env
open Jc_output
open Ml_ocaml.Types
open Ml_ocaml.Ident
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

let rec make_type mlt =
  match mlt.desc with
    | Tvar -> failwith "ml_type.ml: make_type: Tvar"
    | Tarrow _ -> failwith "ml_type.ml: make_type: Tarrow"
    | Ttuple _ -> failwith "ml_type.ml: make_type: Ttuple"
    | Tconstr(path, args, _) ->
	begin match Ml_ocaml.Path.name path with
	  | "unit" -> MLTnative Tunit
	  | "int" -> MLTnative Tinteger
	  | "float" -> MLTnative Treal
	  | "bool" -> MLTnative Tboolean
	  | name ->
	      let ty = Hashtbl.find ml_types name in
	      failwith ("found type "^ty.ml_ty_name)
	end
    | Tobject _ -> failwith "ml_type.ml: make_type: Tobject"
    | Tfield _ -> failwith "ml_type.ml: make_type: Tfield"
    | Tnil -> failwith "ml_type.ml: make_type: Tnil"
    | Tlink t -> make_type t
    | Tsubst _ -> failwith "ml_type.ml: make_type: Tsubst"
    | Tvariant _ -> failwith "ml_type.ml: make_type: Tvariant"
    | Tunivar -> failwith "ml_type.ml: make_type: Tunivar"
    | Tpoly _ -> failwith "ml_type.ml: make_type: Tpoly"

let make mlt =
  match make_type mlt with
    | MLTnative t ->
	JCTnative t
    | MLTrecord(si, _)
    | MLTvariant(si, _, _) ->
	JCTpointer(si, Some(Num.num_of_int 0), Some(Num.num_of_int 0))

let label ld =
  match make_type ld.lbl_res with
    | MLTrecord(_, lbls) -> List.assoc ld.lbl_name lbls
    | _ -> failwith "ml_type.ml: label: not a record type"

let constructor cd =
  match make_type cd.cstr_res with
    | MLTvariant(_, _, constrs) -> List.assoc cd.cstr_name constrs
    | _ -> failwith "ml_type.ml: constructor: not a variant type"

let jc_decl name = function
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
	 (fun _ ty acc -> (jc_decl name ty)::acc)
	 ty.ml_ty_instances
	 acc)
    ml_types
    []

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
