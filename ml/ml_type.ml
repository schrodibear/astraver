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
  ml_ci_structure: Jc_env.struct_info;
  ml_ci_arguments: Jc_env.field_info list;
}

type ml_jessie_type =
  | MLTnot_closed
  | MLTnative of native_type
  | MLTrecord of Jc_env.struct_info * (string * ml_label_info) list
  | MLTvariant of Jc_env.variant_info * (string * ml_constructor_info) list
  | MLTtuple of Jc_env.struct_info
  | MLTlogic of string

module ComparableCamlTypeList = struct
  type t = type_expr list

  let rec compare_lists f l1 l2 = match l1, l2 with
    | [], [] -> 0
    | x1::rem1, x2::rem2 ->
	let r = f x1 x2 in
	if r = 0 then compare_lists f rem1 rem2 else r
    | _::_, [] -> 1
    | [], _::_ -> -1

  let rec compare_types a b = match a.desc, b.desc with
    | Tvar, Tvar -> Pervasives.compare a.id b.id
    | Tlink a', _ -> compare_types a' b
    | _, Tlink b' -> compare_types a b'
    | Tconstr(p1, al1, _), Tconstr(p2, al2, _) ->
	let r = String.compare
	  (Ml_ocaml.Path.name p1)
	  (Ml_ocaml.Path.name p2)
	in
	if r = 0 then compare_lists compare_types al1 al2 else r
    | _ -> Pervasives.compare a b

  let rec compare = compare_lists compare_types
end

module ParamMap = Map.Make(ComparableCamlTypeList)

type ml_caml_type = {
  ml_ty_name: string;
  ml_ty_decl: Ml_ocaml.Types.type_declaration;
  ml_ty_logic: bool; (* unused, actually (using "Type_abstract" instead) *)
  mutable ml_ty_instances: ml_jessie_type ParamMap.t;
  mutable ml_ty_invariants: (string * Jc_env.var_info * Jc_ast.assertion) list;
}

let ml_types = Hashtbl.create 11 (* string -> ml_caml_type *)
let ml_tuples = ref ParamMap.empty (* Ml_env.struct_info *)

let declare id td logic =
  let n = name id in
  Hashtbl.add ml_types n {
    ml_ty_name = n;
    ml_ty_decl = td;
    ml_ty_logic = logic;
    ml_ty_instances = ParamMap.empty;
    ml_ty_invariants = [];
  }

let add_invariant id inv =
  let mlty = Hashtbl.find ml_types (name id) in
  mlty.ml_ty_invariants <- inv::mlty.ml_ty_invariants

exception Not_closed

let rec make_type mlt =
  let not_implemented = not_implemented none in
  match mlt.desc with
    | Tvar -> raise Not_closed
    | Tarrow _ -> not_implemented "ml_type.ml: make_type: Tarrow"
    | Ttuple tl ->
	begin try
	  MLTtuple(ParamMap.find tl !ml_tuples)
	with Not_found ->
	  let jcty = tuple tl in
	  ml_tuples := ParamMap.add tl jcty !ml_tuples;
	  MLTtuple jcty
	end
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
    | MLTtuple si ->
	make_valid_pointer (JCtag si)
    | MLTvariant(vi, _) ->
	make_valid_pointer (JCvariant vi)
    | MLTlogic x ->
	JCTlogic x

and instance args ty =
  log "Instanciate type %s with %d/%d arguments." ty.ml_ty_name
    (List.length args) ty.ml_ty_decl.type_arity;
  match ty.ml_ty_decl.type_kind with
    | Type_abstract ->
	MLTlogic(fresh_ident ty.ml_ty_name)
    | Type_record(ll, _, _) ->
	let vi = make_variant (fresh_ident ty.ml_ty_name) in
	let si = make_root_struct vi (fresh_ident ty.ml_ty_name) in
	(* temporary declaration in case of recursive type definition *)
	ty.ml_ty_instances <- ParamMap.add
	  args (MLTrecord(si, [])) ty.ml_ty_instances;
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
	let vi = make_variant (fresh_ident ty.ml_ty_name) in
	(* temporary declaration in case of recursive type definition *)
	ty.ml_ty_instances <- ParamMap.add
	  args (MLTvariant(vi, [])) ty.ml_ty_instances;
	let constrs = List.map
	  (fun (name, cargs) ->
	     let si = make_root_struct vi (fresh_ident name) in
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
	       ml_ci_structure = si;
	       ml_ci_arguments = fi_args;
	     } in
	     name, ci)
	  cl
	in
	MLTvariant(vi, constrs)

and tuple tl =
  let vi = make_variant (fresh_ident "jessica_tuple") in
  let si = make_root_struct vi (fresh_ident "jessica_tuple") in
  list_iteri
    (fun i ty -> ignore (make_field si ("f"^string_of_int i) (make ty)))
    tl;
  si.jc_struct_info_fields <- List.rev si.jc_struct_info_fields;
  si

let structure ty =
  match make_type ty with
    | MLTrecord(si, _)
    | MLTtuple si -> si
    | _ -> failwith "ml_type.ml: structure: not translated to a structure type"

let label recty ld =
  match make_type recty with
    | MLTrecord(_, lbls) -> List.assoc ld.lbl_name lbls
    | _ -> failwith "ml_type.ml: label: not a record type"

let constructor varty cd =
  match make_type varty with
    | MLTvariant(_, constrs) -> List.assoc cd.cstr_name constrs
    | _ -> failwith "ml_type.ml: constructor: not a variant type"

let proj tty index =
  match make_type tty with
    | MLTtuple si -> List.nth si.jc_struct_info_fields index
    | _ -> failwith "ml_type.ml: constructor: not a tuple type"

let get_variant si = match si.jc_struct_info_variant with
  | None -> raise (Invalid_argument "ml_type.ml, get_variant")
  | Some vi -> vi

(** Type interpretation *)
let jc_decl mlty = function
  | MLTnot_closed ->
      assert false
  | MLTnative t ->
      [ JClogic_type_def mlty.ml_ty_name ]
  | MLTrecord(si, lbls) ->
      [ make_variant_def (get_variant si);
	JCstruct_def(
	  si.jc_struct_info_name,
	  (match si.jc_struct_info_parent with
	     | None -> None
	     | Some si -> Some si.jc_struct_info_name),
	  List.map (fun (_, l) -> l.ml_li_field) lbls,
	  mlty.ml_ty_invariants
	)]
  | MLTvariant(vi, constrs) ->
      let c_defs = List.map
	(fun (_, ci) ->
	   let si = ci.ml_ci_structure in
	   JCstruct_def(
	     si.jc_struct_info_name,
	     None,
	     ci.ml_ci_arguments,
	     mlty.ml_ty_invariants
	   ))
	constrs
      in
      (make_variant_def vi)::c_defs
  | MLTtuple si ->
      [ make_variant_def (get_variant si);
	make_struct_def si mlty.ml_ty_invariants]
  | MLTlogic x ->
      [ JClogic_type_def x]

let jc_decls () =
  let decls1 = ParamMap.fold
    (fun _ si acc ->
       (make_variant_def (get_variant si)::
	 (make_struct_def si [])::acc))
    !ml_tuples
    []
  in
  let decls2 = Hashtbl.fold
    (fun _ ty acc ->
       ParamMap.fold
	 (fun _ ity acc -> (jc_decl ty ity)@acc)
	 ty.ml_ty_instances
	 acc)
    ml_types
    []
  in
  decls1 @ List.rev decls2

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
