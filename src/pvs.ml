
(*i $Id: pvs.ml,v 1.8 2002-02-05 09:50:29 filliatr Exp $ i*)

open Logic
open Types
open Misc
open Ident
open Format
open Vcg

let relation id =
  if id == t_lt then "<" 
  else if id == t_le then "<="
  else if id == t_gt then ">"
  else if id == t_ge then ">="
  else if id == t_eq then "="
  else if id == t_neq then "/="
  else assert false

let print_term fmt t = 
  let rec print0 = function
    | Tapp (id, [a;b]) when is_relation id ->
	fprintf fmt "@[<hov 2>"; print1 a; 
	fprintf fmt " %s@ " (relation id);
	print1 b; fprintf fmt "@]"
    | t -> 
	print1 t
  and print1 = function
    | Tapp (id, [a;b]) when id == t_add || id == t_sub ->
	fprintf fmt "@[<hov 2>"; print1 a;
	fprintf fmt " %s@ " (if id == t_add then "+" else "-");
	print2 b; fprintf fmt "@]"
    | t ->
	print2 t
  and print2 = function
    | Tapp (id, [a;b]) when id == t_mul || id == t_div ->
	fprintf fmt "@[<hov 2>"; print2 a;
	fprintf fmt " %s@ " (if id == t_mul then "*" else "/");
	print3 b; fprintf fmt "@]"
    | t ->
	print3 t
  and print3 = function
    | Tconst (ConstInt n) -> 
	fprintf fmt "%d" n
    | Tconst (ConstBool b) -> 
	fprintf fmt "%b" b
    | Tconst ConstUnit -> 
	fprintf fmt "unit" 
    | Tconst (ConstFloat f) -> 
	(* TODO *)
	assert (floor f = f);
	fprintf fmt "%d" (truncate f)
    | Tbound _ ->
	assert false
    | Tvar id | Tapp (id, []) -> 
	fprintf fmt "%s" (Ident.string id)
    | Tapp (id, [t]) when id == t_neg ->
	fprintf fmt "-"; print3 t
    | Tapp (id, l) as t when is_relation id || is_arith id ->
	fprintf fmt "@[("; print0 t; fprintf fmt ")@]"
    | Tapp (id, tl) -> 
	fprintf fmt "%s(@[" (Ident.string id);
	print_list fmt 
	  (fun fmt () -> fprintf fmt ",@ ") (fun _ t -> print0 t) tl;
	fprintf fmt "@])"
  in
  print0 t

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTfloat -> fprintf fmt "real"
  | PTarray (_, v) -> 
      fprintf fmt "[int -> "; print_pure_type fmt v; fprintf fmt "]"
  | PTexternal id -> fprintf fmt "%s" (Ident.string id)

let print_predicate fmt p =
  let rec print0 = function
    | Pif (a, b, c) -> 
	fprintf fmt "@[IF "; print_term fmt a; fprintf fmt "@ THEN ";
	print0 b; fprintf fmt "@ ELSE "; print0 c; fprintf fmt " ENDIF@]"
    | Pimplies (a, b) -> 
	fprintf fmt "(@["; print1 a; fprintf fmt " IMPLIES@ "; print0 b;
	fprintf fmt "@])"
    | p -> print1 p
  and print1 = function
    | Por (a, b) -> print1 a; fprintf fmt " OR@ "; print2 b
    | p -> print2 p
  and print2 = function
    | Pand (a, b) -> print2 a; fprintf fmt " AND@ "; print3 b
    | p -> print3 p
  and print3 = function
    | Pvar id -> Ident.print fmt id
    | Papp (id, l) -> 	
	fprintf fmt "%s(@[" (Ident.string id);
	print_list fmt (fun fmt () -> fprintf fmt ",@ ") print_term l;
	fprintf fmt "@])"
    | Pnot p -> fprintf fmt "NOT "; print3 p
    | Forall (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = bsubst_in_predicate [n, Tvar id'] p in
	fprintf fmt "(@[FORALL (%s: " (Ident.string id');
	print_pure_type fmt t; fprintf fmt "):@ ";
	print0 p'; fprintf fmt "@])"
    | p -> fprintf fmt "("; print0 p; fprintf fmt ")"
  in
  print0 p

let rec print_type_v fmt = function
  | PureType pt -> print_pure_type fmt pt
  | Ref v -> print_type_v fmt v
  | Array (_, v) -> fprintf fmt "[int -> "; print_type_v fmt v; fprintf fmt "]"
  | Arrow _ -> assert false

let occur_sequent id = function
  | Spred p -> occur_predicate id p
  | Svar _ -> false

let print_sequent fmt (hyps,concl) =
  let rec print_seq = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	if List.exists (occur_sequent id) hyps || occur_predicate id concl then
	begin
	  fprintf fmt "FORALL (%s: " (Ident.string id); 
	  print_type_v fmt v; fprintf fmt ") :@\n"
	end;
	print_seq hyps
    | Spred p :: hyps -> 
	print_predicate fmt p; fprintf fmt " IMPLIES@\n";
	print_seq hyps
  in
  print_seq hyps

let print_lemma fmt (id,s) =
  fprintf fmt "  @[<hov 2>%s: LEMMA@\n" id;
  print_sequent fmt s;
  fprintf fmt "@]@\n"

let print_obligations fmt ol = 
  print_list fmt (fun fmt () -> fprintf fmt "@\n") print_lemma ol;
  if ol <> [] then fprintf fmt "@\n"

let begin_theory fmt th =
  fprintf fmt "%s: THEORY@\nBEGIN@\n@\n" th;
  fprintf fmt "  unit: TYPE = int@\n@\n  unit: unit = 0@\n@\n"
    
let end_theory fmt th =
  fprintf fmt "END %s@\n" th


type elem = 
  | Verbatim of string
  | Obligations of obligation list

let queue = Queue.create ()

let reset () = Queue.clear queue

let push_verbatim s = Queue.add (Verbatim s) queue

let push_obligations ol = Queue.add (Obligations ol) queue

let output_elem fmt = function
  | Verbatim s -> fprintf fmt "  %s@\n@\n" s
  | Obligations ol -> print_obligations fmt ol

let output_file fwe =
  let f = fwe ^ "_why.pvs" in
  let cout = open_out f in
  let fmt = formatter_of_out_channel cout in
  let th = Filename.basename fwe in
  begin_theory fmt th;
  Queue.iter (output_elem fmt) queue;
  end_theory fmt th;
  pp_print_flush fmt ();
  close_out cout

