
open Format
open Clogic
open Cast
open Creport
open Info

(* Type equality (i.e. structural equality, but ignoring attributes) *)
(* TODO: pointers = arrays *)

let rec eq_type ty1 ty2 = 
  eq_type_node ty1.ctype_node ty2.ctype_node

and eq_type_node tn1 tn2 = match tn1, tn2 with
  | CTvoid, CTvoid
  | CTint _, CTint _ 
  | CTfloat _, CTfloat _ 
  | CTint _, CTenum _ 
  | CTenum _, CTint _ ->
      true
  | CTvar x1, CTvar x2 ->
      x1 = x2
  | CTarray (ty1, _), CTarray (ty2, _) ->
      eq_type ty1 ty2 (* TODO: taille? *)
  | CTpointer ty1, CTpointer ty2 ->
      eq_type ty1 ty2
  | CTarray (ty1, _), CTpointer ty2 | CTpointer ty1, CTarray (ty2, _) ->
      eq_type ty1 ty2
  | CTstruct (s1, _), CTstruct (s2, _) ->
      s1 = s2
  | CTunion (u1, _), CTunion (u2, _) ->
      u1 = u2
  | CTenum (e1, _), CTenum (e2, _) ->
      e1 = e2
  | CTpointer {ctype_node = CTfun _ as tn1}, (CTfun _ as tn2)
  | (CTfun _ as tn1), CTpointer {ctype_node = CTfun _ as tn2} ->
      eq_type_node tn1 tn2
  | CTfun ([], ty1), CTfun (_, ty2) | CTfun (_, ty1), CTfun ([], ty2) ->
      eq_type ty1 ty2
  | CTfun (pl1, ty1), CTfun (pl2, ty2) ->
      eq_type ty1 ty2 &&
      (try List.for_all2 (fun (ty1,_) (ty2,_) -> eq_type ty1 ty2) pl1 pl2
       with Invalid_argument _ -> false)
  | _ ->
      false

(* [sub_type ty1 ty2] is true if type [ty1] can be coerced to type [ty2] *)

let sub_type ty1 ty2 = match ty1.ctype_node, ty2.ctype_node with
  | CTint _, CTfloat _ -> true
  | CTpointer { ctype_node = CTvoid }, CTpointer _ -> true
  | _ -> eq_type ty1 ty2

let compatible_type ty1 ty2 = sub_type ty1 ty2 || sub_type ty2 ty1

let arith_type ty = match ty.ctype_node with
  | CTint _ | CTfloat _ -> true
  | _ -> false

let array_type ty = match ty.ctype_node with
  | CTarray _ -> true
  | _ -> false

let pointer_type ty = match ty.ctype_node with
  | CTpointer _ -> true
  | _ -> false

let pointer_or_array_type ty = match ty.ctype_node with
  | CTpointer _ | CTarray _ -> true
  | _ -> false

let is_null e = match e.texpr_node with
  | TEconstant (IntConstant s) -> (try int_of_string s = 0 with _ -> false)
  | _ -> false

(*s Global environment *)

(* tagged types *)

type tag_kind = Struct | Union | Enum

let tag_kind = function
  | CTstruct _ -> Struct
  | CTunion _ -> Union
  | CTenum _ -> Enum
  | _ -> assert false

type tag_type_definition = Incomplete | Defined of texpr ctype_node

type tag_type = { 
  tag_kind : tag_kind;
  tag_name : string; (* original source name *)
  tag_uname: string; (* unique name used for further reference *)
  mutable tag_type : tag_type_definition;
}

(* map from unique names to tagged types *)
let (tags_t : (string, tag_type) Hashtbl.t) = Hashtbl.create 97

let tag_type_definition n = 
  let tt = Hashtbl.find tags_t n in tt.tag_type

let create_tag_type k n ty =
  let rec fresh i = 
    let un = n ^ "_" ^ string_of_int i in
    if Hashtbl.mem tags_t un then fresh (succ i) else un
  in
  let un = if Hashtbl.mem tags_t n then fresh 0 else n in
  let tt = 
    { tag_kind = k; tag_name = n; 
      tag_uname = un; tag_type = ty } 
  in
  Hashtbl.add tags_t un tt;
  tt

let clash_tag l s1 s2 = 
  let redef t n = error l (sprintf "redeclaration of `%s %s'" t n) in
  match s1, s2 with
  | CTstruct (n,_), CTstruct _ -> redef "struct" n
  | CTunion (n,_), CTunion _ -> redef "union" n
  | CTenum (n,_), CTenum _ -> redef "enum" n
  | (CTstruct (n,_) | CTunion (n,_) | CTenum (n,_)), 
    (CTstruct _ | CTunion _ | CTenum _) -> 
      error l (sprintf "`%s' defined as wrong kind of tag" n)
  | _ -> assert false

(* typedefs *)

let typedef_t = (Hashtbl.create 97 : (string, tctype) Hashtbl.t)

let is_typedef = Hashtbl.mem typedef_t

let find_typedef = Hashtbl.find typedef_t

let add_typedef l x ty = 
  if is_typedef x then begin
    if ty = find_typedef x then error l ("redefinition of `" ^ x ^ "'")
    else error l ("conflicting types for `" ^ x ^ "'")
  end else
    Hashtbl.add typedef_t x ty

(* used names (in order to rename heap variables when necessary) *)
let used_names = Hashtbl.create 97
let mark_as_used x = Hashtbl.add used_names x ()
let is_used_name n = Hashtbl.mem used_names n

let use_name ?local_names n = 
  if is_used_name n then raise Exit; 
  begin match local_names with Some h -> if Hashtbl.mem h n then raise Exit | None -> () end;
  n

let rec next_name ?local_names n i = 
  let n_i = n ^ "_" ^ string_of_int i in
  try use_name ?local_names n_i with Exit -> next_name ?local_names n (succ i)

let unique_name ?local_names n = try use_name ?local_names n with Exit -> next_name ?local_names n 0

(* variables and functions *)
let (sym_t : (string, (texpr ctype * var_info)) Hashtbl.t) = Hashtbl.create 97

let is_sym = Hashtbl.mem sym_t

let find_sym = Hashtbl.find sym_t

let add_sym l x ty info = 
  let n = unique_name x in
  mark_as_used n; 
  info.var_unique_name <- n;
  if is_sym x then begin
    let (t,i) = find_sym x in
    if not (eq_type t ty) then 
      (* TODO accepter fonctions avec arguments si aucun la premi�re fois 
	 Question de Claude: accepter aussi un raffinement des specs ? *)
      error l ("conflicting types for " ^ x);
    i
  end else begin
    Hashtbl.add sym_t x (ty,info);
    info
  end

(*s Environments for the logical side *)

let functions = 
  (Hashtbl.create 97 : 
     (string, tctype list * tctype * Info.logic_info) Hashtbl.t)
let add_fun = Hashtbl.add functions
let find_fun = Hashtbl.find functions

let predicates = 
  (Hashtbl.create 97 : (string, tctype list * Info.logic_info) Hashtbl.t) 
let add_pred = Hashtbl.add predicates
let find_pred = Hashtbl.find predicates

(*s Environments for local variables and local structs/unions/enums *)

module Env = struct

  module M = Map.Make(String)

  (* [tags] is the stack of blocks; 
     each block maps a tag name to a tag type *)
  type t = { 
    vars : (texpr ctype * var_info) M.t; 
    used_names : (string, unit) Hashtbl.t;
    tags : (string, tag_type) Hashtbl.t list;
  }

  (* note: the first hash table in [tags] is shared *)
  let shared_hash_table = Hashtbl.create 17

  let empty () = 
    { vars = M.empty; 
      used_names = Hashtbl.create 97; 
      tags = [shared_hash_table] }

  let new_block env = { env with tags = Hashtbl.create 17 :: env.tags }

  (* symbols *)
  let add x t info env = 
    let n = unique_name ~local_names:env.used_names x in
    info.var_unique_name <- n;
    Hashtbl.add env.used_names n ();
    { env with vars = M.add x (t,info) env.vars }

  let find x env = M.find x env.vars

  let mem x env = M.mem x env.vars

  (* tagged type *)
  let find_tag n env =
    let rec find = function
      | [] -> raise Not_found
      | h :: hl -> try Hashtbl.find h n with Not_found -> find hl
    in
    find env.tags

  let find_tag_type loc env tyn = 
    let tt = match tyn with
      | CTstruct (n, Tag) | CTunion (n, Tag) | CTenum (n, Tag) ->
          (try
	     find_tag n env
	   with Not_found -> 
	     let tt = create_tag_type (tag_kind tyn) n Incomplete in
	     Hashtbl.add (List.hd env.tags) n tt;
	     tt)
      | CTstruct (n, _) | CTunion (n, _) | CTenum (n, _) ->
	   (try
              let tt = Hashtbl.find (List.hd env.tags) n in
	      begin match tt.tag_type with
		| Incomplete ->
                    (* tag already seen in this block but not yet defined *)
                    tt.tag_type <- Defined tyn
		| Defined tyn' ->  
		    (* tag [n] already defined in current block *)
		    clash_tag loc tyn tyn'
	      end;
	      tt
	    with Not_found ->
	      let tt = create_tag_type (tag_kind tyn) n (Defined tyn) in
	      Hashtbl.add (List.hd env.tags) n tt;
	      tt)
      | _ ->
	  assert false
    in
    match tt.tag_kind with
      | Struct -> CTstruct (tt.tag_uname, Tag)
      | Union -> CTunion (tt.tag_uname, Tag)
      | Enum -> CTenum (tt.tag_uname, Tag)

end

(* Field access *)

let fields_t = Hashtbl.create 97
let find_field ~tag:n ~field:x = 
  try 
    Hashtbl.find fields_t (n,x)
  with Not_found -> 
    let u = 
      try use_name x with Exit -> 
	let n_x = n ^ "_" ^ x in 
	try use_name n_x with Exit -> 
	  next_name n_x 0
    in
    let f = { field_name = x; field_tag = n; field_heap_var_name = u } in
    mark_as_used u; 
    Hashtbl.add fields_t (n,x) f; f

let declare_fields tyn fl = match tyn with
  | CTstruct (n, _) | CTunion (n, _) ->
      List.iter (fun (_,x,_) -> ignore (find_field n x)) fl
  | _ -> 
      assert false
  
let type_of_field loc x ty = 
  let rec lookup su n = function
    | [] -> error loc (su ^ " has no member named `" ^ x ^ "'")
    | (ty, y, _) :: _ when x = y -> find_field n x, ty
    | _ :: fl -> lookup su n fl
  in
  match ty.ctype_node with
    | CTstruct (n, Tag) | CTunion (n, Tag) -> 
        assert (Hashtbl.mem tags_t n);
	let tt = Hashtbl.find tags_t n in
	begin match tt.tag_type with
	  | Incomplete -> error loc ("use of incomplete type")
	  | Defined (CTstruct (_, Decl fl)) -> lookup "structure" n fl
	  | Defined (CTunion (_, Decl fl)) -> lookup "union" n fl
	  | Defined _ ->
	      error loc ("request for member `" ^ x ^ 
			 "' in something not a structure or union")
	end
    | CTstruct _ | CTunion _ -> assert false
    | _ -> error loc ("request for member `" ^ x ^ 
		      "' in something not a structure or union")

