(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.ml,v 1.16 2002-03-19 14:31:50 filliatr Exp $ i*)

open Options
open Logic
open Types
open Ast
open Misc
open Util
open Ident
open Format
open Vcg

let out_file f = f ^ "_why.v"

let relation id =
  if id == t_lt then "<" 
  else if id == t_le then "<="
  else if id == t_gt then ">"
  else if id == t_ge then ">="
  else if id == t_eq then "="
  else if id == t_neq then "<>"
  else assert false

let inz = ref 0
let openz fmt = if !inz == 0 then fprintf fmt "`@["; incr inz 
let closez fmt = decr inz; if !inz == 0 then fprintf fmt "@]`"

let print_term fmt t = 
  let rec print0 = function
    | Tapp (id, [a;b]) when is_relation id ->
	fprintf fmt "(@[<hov 2>Z%s_bool@ " (Ident.string id);
	print1 a; fprintf fmt "@ "; print1 b; fprintf fmt "@])"
    | t -> 
	print1 t
  and print1 = function
    | Tapp (id, [a;b]) when id == t_add || id == t_sub ->
	openz fmt; print1 a;
	fprintf fmt " %s@ " (if id == t_add then "+" else "-");
	print2 b; closez fmt
    | t ->
	print2 t
  and print2 = function
    | Tapp (id, [a;b]) when id == t_mul || id == t_div ->
	openz fmt; print2 a;
	fprintf fmt " %s@ " (if id == t_mul then "*" else "/");
	print3 b; closez fmt
    | t ->
	print3 t
  and print3 = function
    | Tconst (ConstInt n) -> 
	openz fmt; fprintf fmt "%d" n; closez fmt
    | Tconst (ConstBool b) -> 
	fprintf fmt "%b" b
    | Tconst ConstUnit -> 
	fprintf fmt "tt" 
    | Tconst (ConstFloat f) -> 
	(* TODO *)
	assert (floor f = f);
	openz fmt; fprintf fmt "%d" (truncate f); closez fmt
    | Tbound _ ->
	assert false
    | Tvar id when id == t_zwf_zero ->
	fprintf fmt "(Zwf ZERO)"
    | Tvar id | Tapp (id, []) -> 
	fprintf fmt "%s" (Ident.string id)
    | Tapp (id, [t]) when id == t_neg ->
	openz fmt; fprintf fmt "-"; print3 t; closez fmt
    | Tapp (id, l) as t when is_relation id || is_arith id ->
	fprintf fmt "@[("; print0 t; fprintf fmt ")@]"
    | Tapp (id, tl) when id == t_zwf_zero -> 
	openz fmt;
	fprintf fmt "(@[Zwf 0 "; print_terms tl; fprintf fmt "@])";
	closez fmt
    | Tapp (id, tl) -> 
	fprintf fmt "(@[%s " (Ident.string id); print_terms tl;
	fprintf fmt "@])"
  and print_terms tl =
    print_list (fun fmt () -> fprintf fmt "@ ") (fun _ t -> print0 t) fmt tl
  in
  print0 t

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "Z"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTfloat -> fprintf fmt "R"
  | PTarray (s, v) -> 
      fprintf fmt "(array "; print_term fmt s; fprintf fmt " "; 
      print_pure_type fmt v; fprintf fmt ")"
  | PTexternal id -> fprintf fmt "%s" (Ident.string id)

let print_predicate fmt p =
  let rec print0 = function
    | Pif (a, b, c) -> 
	fprintf fmt "(@[if "; print_term fmt a; fprintf fmt "@ then ";
	print0 b; fprintf fmt "@ else "; print0 c; fprintf fmt "@])"
(*i
	fprintf fmt "((@["; print1 a; fprintf fmt " ->@ "; print0 b; 
	fprintf fmt ") /\@ (~"; print3 a; fprintf fmt " ->@ "; print0 c; 
	fprintf fmt "@]))"
i*)
    | Pimplies (a, b) -> 
	fprintf fmt "(@["; print1 a; fprintf fmt " ->@ "; print0 b;
	fprintf fmt "@])"
    | p -> print1 p
  and print1 = function
    | Por (a, b) -> print1 a; fprintf fmt " \/@ "; print2 b
    | p -> print2 p
  and print2 = function
    | Pand (a, b) -> print2 a; fprintf fmt " /\@ "; print3 b
    | p -> print3 p
  and print3 = function
    | Ptrue -> fprintf fmt "True"
    | Pfalse -> fprintf fmt "False"
    | Pvar id -> Ident.print fmt id
    | Papp (id, [a;b]) when id == t_eq ->
	fprintf fmt "@[%a =@ %a@]" print_term a print_term b
    | Papp (id, [t]) when id == well_founded ->
	fprintf fmt "@[(well_founded ?@ "; print_term fmt t; fprintf fmt ")@]"
    | Papp (id, [a;b]) when id == t_neq ->
	fprintf fmt "~("; 
	print_term fmt a; fprintf fmt " =@ "; print_term fmt b;
	fprintf fmt ")"
    | Papp (id, [a;b]) when id == t_zwf_zero ->
	fprintf fmt "(Zwf `0` "; 
	print_term fmt a; fprintf fmt " ";
	print_term fmt b; fprintf fmt ")"
    | Papp (id, [a;b]) when is_comparison id ->
	openz fmt; print_term fmt a; 
	fprintf fmt " %s@ " (relation id);
	print_term fmt b; closez fmt
    | Papp (id, l) ->
	fprintf fmt "(@[%s " (Ident.string id); 
	print_list (fun fmt () -> fprintf fmt "@ ") print_term fmt l;
	fprintf fmt "@])"
    | Pnot p -> fprintf fmt "~"; print3 p
    | Forall (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = bsubst_in_predicate [n, Tvar id'] p in
	fprintf fmt "(@[(%s:" (Ident.string id');
	print_pure_type fmt t; fprintf fmt ")@ ";
	print0 p'; fprintf fmt "@])"
    | p -> fprintf fmt "("; print0 p; fprintf fmt ")"
  in
  print0 p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray (s, v) -> 
      fprintf fmt "(array %a %a)" print_term s print_cc_type v
  | TTlambda _
  | TTarrow _ 
  | TTtuple _ -> 
      assert false

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
	  fprintf fmt "(%s: " (Ident.string id); 
	  print_cc_type fmt v; fprintf fmt ") @\n"
	end;
	print_seq hyps
    | Spred p :: hyps -> 
	print_predicate fmt p; fprintf fmt " ->@\n";
	print_seq hyps
  in
  print_seq hyps

let print_lemma fmt (id,s) =
  fprintf fmt "@[<hov 2>Lemma %s : @\n" id;
  print_sequent fmt s;
  fprintf fmt ".@]@\n"

let print_obligation fmt o = 
  print_lemma fmt o;
  fprintf fmt "Proof.@\n(* FILL PROOF HERE *)@\nSave.@\n@\n"


(*s Queueing elements. *)

let oblig = Hashtbl.create 97

let queue = Queue.create ()

let reset () = Queue.clear queue; Hashtbl.clear oblig

let push_obligations ol = 
  List.iter (fun o -> Queue.add o queue) ol;
  List.iter (fun (l,p) -> Hashtbl.add oblig l p) ol


(*s Generating the output. *)

let po_regexp = Str.regexp "Lemma[ ]+\\(.*_po_[0-9]+\\)[ ]*:[ ]*"

let is_po s =
  try
    if Str.string_match po_regexp s 0 then
      Some (Str.matched_group 1 s)
    else
      None
  with Not_found ->
    None

let regen oldf fmt =
  let cin = open_in oldf in
  let rec scan () =
    let s = input_line cin in
    match is_po s with
      | Some l ->
	  if Hashtbl.mem oblig l then begin
	    if !verbose then eprintf "overwriting obligation %s@\n" l;
	    let p = Hashtbl.find oblig l in
	    print_lemma fmt (l,p);
	    Hashtbl.remove oblig l
	  end else
	    if !verbose then eprintf "erasing obligation %s@\n" l;
	  skip_to_dot ();
	  scan ()
      | _ -> 
	  fprintf fmt "%s@\n" s;
	  scan ()
  and skip_to_dot () =
    let s = input_line cin in
    let n = String.length s in
    if n = 0 || s.[n-1] <> '.' then skip_to_dot ()
  and tail () = 
    fprintf fmt "%c" (input_char cin); tail () 
  in
  begin
    try scan () with End_of_file -> 
    try tail () with End_of_file -> close_in cin
  end;
  Queue.iter 
    (function (l,_) as o -> if Hashtbl.mem oblig l then print_obligation fmt o)
    queue

let first_time fmt =
  Queue.iter (print_obligation fmt) queue

let print_in_file p f =
  let cout = open_out f in
  let fmt = formatter_of_out_channel cout in
  p fmt;
  pp_print_flush fmt ();
  close_out cout

let output_file fwe =
  let f = fwe ^ "_why.v" in
  if Sys.file_exists f then begin
    let fbak = f ^ ".bak" in
    Sys.rename f fbak; 
    if_verbose_3 eprintf "*** re-generating file %s (backup in %s)@." f fbak;
    print_in_file (regen fbak) f
  end else begin
    if_verbose_2 eprintf "*** generating file %s@." f;
    print_in_file first_time f
  end
