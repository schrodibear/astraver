
open Jc_envset
open Jc_fenv
open Jc_ast

let rec term this t =
  match t.jc_term_node with
    | JCTconst _ -> ()
    | JCTif (_, _, _) -> assert false (* TODO *)
    | JCTcast (t, ty) -> term this t
    | JCTinstanceof (t, ty) -> term this t
    | JCToffset_min t 
    | JCToffset_max t -> term this t
    | JCTold t -> term this t
    | JCTapp (id, l) ->
	if FieldSet.is_empty id.jc_logic_info_effects.jc_reads_fields
	then List.iter (term this) l
	else
	  Jc_typing.typing_error t.jc_term_loc
	    "this call is not allowed in structure invariant"
    | JCTderef (t1, fi) -> 
	begin
	  match t1.jc_term_node with
	    | JCTvar vi when vi == this -> ()
	    | _ -> 
		Jc_typing.typing_error t.jc_term_loc
		  "this dereferencing is not allowed in structure invariant"
	end
    | JCTshift (t1, t2) -> term this t1; term this t2
    | JCTvar _ -> ()

let rec assertion this p =
  match p.jc_assertion_node with
    | JCAtrue | JCAfalse -> ()
    | JCAif (_, _, _) -> assert false (* TODO *)
    | JCAinstanceof(t,_)
    | JCAbool_term t -> term this t
    | JCAold p -> assertion this p
    | JCAforall (id, p) -> assertion this p
    | JCAapp (id, l) ->
	if FieldSet.is_empty id.jc_logic_info_effects.jc_reads_fields
	then List.iter (term this) l
	else
	  Jc_typing.typing_error p.jc_assertion_loc
	    "this call is not allowed in structure invariant"
    | JCAnot p -> assertion this p
    | JCAiff (p1, p2)
    | JCAimplies (p1, p2) -> assertion this p1; assertion this p2
    | JCAand l -> List.iter (assertion this) l


let check invs =
  List.iter
    (fun (li,p) -> 
       match li.jc_logic_info_parameters with
	 | [this] -> assertion this p
	 | _ -> assert false)
    invs


  
(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
