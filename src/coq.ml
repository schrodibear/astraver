(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.ml,v 1.21 2002-03-21 15:47:06 filliatr Exp $ i*)

open Options
open Logic
open Types
open Ast
open Ident
open Util
open Format
open Vcg
open Misc

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
    | Ptrue -> 
	fprintf fmt "True"
    | Pfalse -> 
	fprintf fmt "False"
    | Pvar id -> 
	Ident.print fmt id
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
    | Pnot p -> 
	fprintf fmt "~"; print3 p
    | Forall (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = bsubst_in_predicate [n, Tvar id'] p in
	fprintf fmt "(@[(%s:" (Ident.string id');
	print_pure_type fmt t; fprintf fmt ")@ ";
	print0 p'; fprintf fmt "@])"
    | p -> 
	fprintf fmt "("; print0 p; fprintf fmt ")"
  in
  print0 p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray (s, v) -> 
      fprintf fmt "(array %a %a)" print_term s print_cc_type v
  | TTlambda (b, t) ->
      fprintf fmt "[%a]%a" print_binder b print_cc_type t
  | TTarrow (b, t) -> 
      fprintf fmt "(%a)%a" print_binder b print_cc_type t
  | TTtuple ([_,t], None) -> 
      print_cc_type fmt t
  | TTtuple (bl, None) ->
      fprintf fmt "(tuple_%d %a)" (List.length bl) 
	(print_list space (fun fmt (_,t) -> print_cc_type fmt t)) bl
  | TTtuple (bl, Some q) -> 
      fprintf fmt "(sig_%d %a %a(%a))" (List.length bl)
	(print_list space (fun fmt (_,t) -> print_cc_type fmt t)) bl 
	(print_list nothing 
	     (fun fmt (id,t) -> 
		fprintf fmt "[%a:%a]" Ident.print id print_cc_type t)) bl
	print_predicate q

and print_binder fmt (id,b) = 
  Ident.print fmt id;
  match b with
    | CC_pred_binder p -> fprintf fmt ": %a" print_predicate p
    | CC_var_binder t -> fprintf fmt ": %a" print_cc_type t
    | CC_untyped_binder -> ()

let print_sequent fmt (hyps,concl) =
  let rec print_seq = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "(%a: @[%a@])@\n" Ident.print id print_cc_type v;
	print_seq hyps
    | Spred (id, p) :: hyps -> 
	fprintf fmt "(%a: @[%a@])@\n" Ident.print id print_predicate p;
	print_seq hyps
  in
  print_seq hyps

let print_proof fmt = function
  | Lemma (s, vl) ->
      fprintf fmt "@[(%s %a)@]" s (print_list space Ident.print) vl
  | Reflexivity t ->
      fprintf fmt "@[(refl_equal ? %a)@]" print_term t
  | Assumption id -> 
      Ident.print fmt id

let print_binder_id fmt (id,_) = Ident.print fmt id

let rec print_cc_term fmt = function
  | CC_var id -> 
      Ident.print fmt id
  | CC_letin (_,bl,c,c1) ->
      fprintf fmt "@[@[<hov 2>let (%a) =@ %a in@]@\n%a@]"
      (print_list comma print_binder_id) bl
      print_cc_term c print_cc_term c1
  | CC_lam (b,c) ->
      fprintf fmt "@[<hov 2>[%a]@,%a@]" print_binder b print_cc_term c
  | CC_app (f,args) ->
      fprintf fmt "@[<hov 2>(%a@ %a)@]" 
      print_cc_term f (print_list pp_print_space print_cc_term) args
  | CC_tuple cl ->
      fprintf fmt "<Tuple %a>" (print_list space print_cc_term) cl
  | CC_case _ ->
      fprintf fmt "<Case (TODO)>"
  | CC_if (b,e1,e2) ->
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (print_cc_term fmt) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (print_cc_term fmt) e2;
      fprintf fmt "@]"
  | CC_expr c ->
      fprintf fmt "@["; print_term fmt c; fprintf fmt "@]"
  | CC_hole pr ->
      print_proof fmt pr
  | CC_type t ->
      print_cc_type fmt t
      
let reprint_obligation fmt (id,s) =
  fprintf fmt "@[<hov 2>Lemma %s : @\n%a.@]@\n" id print_sequent s

let print_obligation fmt o = 
  reprint_obligation fmt o;
  fprintf fmt "Proof. (* %s *)@\n(* FILL PROOF HERE *)@\nSave.@\n@\n" (fst o)

let print_validation fmt id v =
  fprintf fmt "@[Definition %s_valid :=@\n  %a.@\n@]@\n" id print_cc_term v

let print_parameter fmt id c =
  fprintf fmt "@[(*Why*) Parameter %s : %a.@\n@]@\n" id print_type_c c

(*s Elements to produce. *)

type element_kind = 
  | Param of string
  | Oblig of string
  | Valid of string

type element = 
  | Parameter of string * type_c
  | Obligation of obligation
  | Validation of string * validation

let elem_t = Hashtbl.create 97 (* maps [element_kind] to [element] *)
let elem_q = Queue.create ()   (* queue of [element_kind * element] *)

let add_elem ek e = Queue.add (ek,e) elem_q; Hashtbl.add elem_t ek e

let reset () = Queue.clear elem_q; Hashtbl.clear elem_t

let push_obligations = 
  List.iter (fun ((l,_) as o) -> add_elem (Oblig l) (Obligation o))

let push_validation id v = 
  add_elem (Valid id) (Validation (id,v))

let print_element_kind fmt = function
  | Param s -> fprintf fmt "parameter %s" s
  | Oblig s -> fprintf fmt "obligation %s" s
  | Valid s -> fprintf fmt "validation %s" s

let print_element fmt = function
  | Parameter (id, c) -> print_parameter fmt id c
  | Obligation o -> print_obligation fmt o
  | Validation (id, v) -> print_validation fmt id v

let reprint_element fmt = function
  | Parameter (id, c) -> print_parameter fmt id c
  | Obligation o -> reprint_obligation fmt o
  | Validation (id, v) -> print_validation fmt id v

(*s Generating the output. *)

let oblig_regexp = Str.regexp "Lemma[ ]+\\(.*_po_[0-9]+\\)[ ]*:[ ]*"
let valid_regexp = Str.regexp "Definition[ ]+\\(.*\\)_valid[ ]*:=[ ]*"
let param_regexp = Str.regexp "(*Why*) Parameter[ ]+\\(.*\\)[ ]*:[ ]*"

let check_line s =
  let test r = 
    if Str.string_match r s 0 then Str.matched_group 1 s else raise Exit
  in
  try Some (Oblig (test oblig_regexp)) with Exit ->
  try Some (Valid (test valid_regexp)) with Exit ->
  try Some (Param (test param_regexp)) with Exit ->
  None

let regen oldf fmt =
  let cin = open_in oldf in
  let rec scan () =
    let s = input_line cin in
    match check_line s with
      | None -> 
	  fprintf fmt "%s@\n" s;
	  scan ()
      | Some e ->
	  if Hashtbl.mem elem_t e then begin
	    if !verbose then eprintf "overwriting %a@\n" print_element_kind e;
	    print_up_to e
	  end else
	    if !verbose then eprintf "erasing %a@\n" print_element_kind e;
	  skip_to_dot ();
	  scan ()
  and skip_to_dot () =
    let s = input_line cin in
    let n = String.length s in
    if n = 0 || s.[n-1] <> '.' then skip_to_dot ()
  and tail () = 
    fprintf fmt "%c" (input_char cin); tail () 
  and print_up_to e =
    let (e',ee) = Queue.take elem_q in
    Hashtbl.remove elem_t e'; 
    if e = e' then 
      reprint_element fmt ee 
    else begin
      print_element fmt ee; print_up_to e
    end
  in
  begin
    try scan () with End_of_file -> 
    try tail () with End_of_file -> close_in cin
  end;
  Queue.iter (fun (_,e) -> print_element fmt e) elem_q

let first_time fmt =
  fprintf fmt "\
(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)@\n
Require Why.@\n@\n";
  Queue.iter (fun (_,e) -> print_element fmt e) elem_q

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
