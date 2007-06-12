
(* Mix to Why *)

open Format
open Mix_ast
open Mix_seq

let interp cl =
  cl (* assert false TODO*)

let print_why_code fmt c =
  begin match c.seq_pre with
    | Some p -> fprintf fmt "pre { %s }@\n" (X.string_of_predicate p)
    | None -> ()
  end;
  fprintf fmt "code %s@\n@\n" (X.string_of_stmt c.seq_code)


