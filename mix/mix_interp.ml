
(* Mix to Why *)

open Format
open Mix_ast
open Mix_seq.X
open Mix_seq

type why_stmt = 
  | Wvoid
  | Wassume of predicate
  | Wassert of predicate
  | Wseq of why_stmt * why_stmt

type why_code = { why_pre : predicate option; why_code : why_stmt }

let rec interp_stmt = function
  | Void -> Wvoid
  | Mix { node = PSassert p } -> Wassert p
  | Mix _ -> Wvoid (* todo *)
  | Assume p -> Wassume p
  | Seq (s1, s2) -> Wseq (interp_stmt s1, interp_stmt s2)

let interp_seq c = { why_pre = c.seq_pre; why_code = interp_stmt c.seq_code }

let interp = List.map interp_seq

(* pretty-printing *)

let counter = ref 0

let rec print_why fmt = function
  | Wvoid -> fprintf fmt "void"
  | Wassume p -> fprintf fmt "[{} unit {%s}]" p
  | Wassert p -> fprintf fmt "(assert {%s}; void)" p
  | Wseq (s1, s2) -> fprintf fmt "%a;@ %a" print_why s1 print_why s2

let print_why_code fmt c =
  incr counter;
  fprintf fmt "let seq%d () =@\n" !counter;
  begin match c.why_pre with
    | Some p -> fprintf fmt "  @[<hov 2>{ %s }@]@\n" (X.string_of_predicate p)
    | None -> ()
  end;
  fprintf fmt "  @[<hv>%a@]@\n@\n" print_why c.why_code


