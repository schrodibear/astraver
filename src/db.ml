(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: db.ml,v 1.17 2002-03-19 12:59:33 filliatr Exp $ i*)

(*s Names separation *)

open Logic
open Types
open Ast
open Env

module Ids = Ident.Idset

let lookup_var ids locop id =
  if Ids.mem id ids then
    None
  else begin
    try Some (Tvar id)
    with Not_found -> Error.unbound_variable id locop
  end

let check_ref idl loc id =
  if (not (Ids.mem id idl)) && (not (Env.is_global id)) then
    Error.unbound_reference id (Some loc)

(*s Crossing binders *)

let rec db_binders loc ((tids,pids,refs) as idl) = function
  | [] -> 
      idl, []
  | (id, BindType (Ref _ | Array _ as v)) :: rem ->
      if is_global id then Error.clash id (Some loc);
      let idl',rem' = db_binders loc (tids,pids,Ids.add id refs) rem in
      idl', (id, BindType v) :: rem'
  | (id, BindType v) :: rem ->
      let idl',rem' = db_binders loc (tids,Ids.add id pids,refs) rem in
      idl', (id, BindType v) :: rem'
  | ((id, BindSet) as t) :: rem ->
      let idl',rem' = db_binders loc (Ids.add id tids,pids,refs) rem in
      idl', t :: rem'
  | a :: rem ->
      let idl',rem' = db_binders loc idl rem in idl', a :: rem'


(* db patterns *)
(*i
let rec db_pattern = function
  | (PatVar id) as t ->
      (try 
	 (match Nametab.sp_of_id CCI id with
	    | ConstructRef (x,y) -> [], PatConstruct (id,(x,y))
	    | _                  -> [id],t)
       with Not_found -> [id],t)
  | PatAlias (p,id) ->
      let ids,p' = db_pattern p in ids,PatAlias (p',id)
  | PatPair (p1,p2) ->
      let ids1,p1' = db_pattern p1 in
      let ids2,p2' = db_pattern p2 in
      	ids1@ids2, PatPair (p1',p2')
  | PatApp pl ->
      let ids,pl' =
	List.fold_right
	  (fun p (ids,pl) ->
	     let ids',p' = db_pattern p in ids'@ids,p'::pl) pl ([],[]) in
  	ids,PatApp pl'
  | PatConstruct _ ->
      failwith "constructor in a pattern after parsing !"
i*)

(* db programs *)
  
let db_prog e =
  let loc = e.info.loc in
  (* tids = type idents, ids = variables, refs = references and arrays *)
  let rec db_desc ((tids,ids,refs) as idl) = function
    | (Var x) as t ->
	(match lookup_var ids (Some loc) x with
	   | None -> t
	   | Some c -> Expression c)
    | (Acc x) as t ->
	check_ref refs loc x;
	t
    | Aff (x,e1) ->
	check_ref refs loc x;
	Aff (x, db idl e1)
    | TabAcc (b,x,e1) ->
	check_ref refs loc x;
	TabAcc(b,x,db idl e1)
    | TabAff (b,x,e1,e2) ->
	check_ref refs loc x;
	TabAff (b,x, db idl e1, db idl e2)
    | Seq bl ->
	Seq (List.map (function
			 | Statement p -> Statement (db idl p)
			 | x -> x) bl)
    | If (e1,e2,e3) ->
	If (db idl e1, db idl e2, db idl e3)
    | While (b,inv,var,e) ->
	While (db idl b, inv, var, db idl e)
	  
    | Lam (bl,e) ->
	let idl',bl' = db_binders loc idl bl in Lam(bl', db idl' e)
    | App (e1,e2,a) ->
	App (db idl e1, db_arg idl e2, a)
    | LetRef (x,e1,e2) ->
	LetRef (x, db idl e1, db (tids,ids,Ids.add x refs) e2)
    | LetIn (x,e1,e2) ->
	LetIn (x, db idl e1, db (tids,Ids.add x ids,refs) e2)
	  
    | Rec (f,bl,v,var,e) ->
	let (tids',ids',refs'),bl' = db_binders loc idl bl in
	Rec (f, bl, v, var, db (tids',Ids.add f ids',refs') e)
    | Expression _ as x -> 
	x
    | Coerce e -> 
	Coerce (db idl e)
	  
  and db_arg ((tids,_,refs) as idl) = function
    | Term ({ desc = Var id } as t) -> 
	if Ids.mem id refs then Refarg (t.info.loc, id) else Term (db idl t)
    | Term t -> Term (db idl t)
    | Type v -> Type v
    | Refarg _ -> assert false

  and db idl e =
    { desc = db_desc idl e.desc ;
      info = { pre = e.info.pre; post = e.info.post; loc = e.info.loc } }

  in
  let vars,refs = all_vars (), all_refs () in
  db (Ids.empty, vars, refs) e

