
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
  else if id == t_noteq then "/="
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
	fprintf fmt "%f" f
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

let print_predicate fmt p =
  let rec print0 = function
    | Pif (a, b, c) -> 
	fprintf fmt "@[IF "; print0 a; fprintf fmt "@ THEN ";
	print0 b; fprintf fmt "@ ELSE "; print0 c; fprintf fmt "@]"
    | Pimplies (a, b) -> print1 a; fprintf fmt " IMPLIES@ "; print0 b
    | p -> print1 p
  and print1 = function
    | Por (a, b) -> print1 a; fprintf fmt " OR@ "; print2 b
    | p -> print2 p
  and print2 = function
    | Pand (a, b) -> print2 a; fprintf fmt " AND@ "; print3 b
    | p -> print3 p
  and print3 = function
    | Pterm t -> print_term fmt t
    | Pnot p -> fprintf fmt "NOT "; print3 p
    | p -> fprintf fmt "("; print0 p; fprintf fmt ")"
  in
  print0 p

let pure_type_id = function
  | PTint -> "int"
  | PTbool -> "bool"
  | PTunit -> "unit"
  | PTfloat -> "real"
  | PTexternal id -> Ident.string id

let rec print_type_v fmt = function
  | PureType pt -> fprintf fmt "%s" (pure_type_id pt)
  | Ref v -> print_type_v fmt v
  | Array (_, v) -> fprintf fmt "[int -> "; print_type_v fmt v; fprintf fmt "]"
  | Arrow _ -> assert false

let print_sequent fmt (hyps,concl) =
  let print_hyp = function
    | Svar (id, v) -> 
	fprintf fmt "FORALL (%s: " (Ident.string id); 
	print_type_v fmt v; fprintf fmt ") :@\n"
    | Spred p -> 
	print_predicate fmt p; fprintf fmt " IMPLIES@\n"
  in
  List.iter print_hyp hyps;
  print_predicate fmt concl

let print_lemma fmt (id,s) =
  fprintf fmt "  @[<hov 2>LEMMA %s:@\n" id;
  print_sequent fmt s;
  fprintf fmt "@]@\n"

let print_obligations fmt ol = 
  print_list fmt (fun fmt () -> fprintf fmt "@\n") print_lemma ol;
  if ol <> [] then fprintf fmt "@\n"

let begin_theory fmt th =
  fprintf fmt "%s: THEORY@\nBEGIN@\n\n" th
    
let end_theory fmt =
  fprintf fmt "END@\n"
