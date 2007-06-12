
(* Mix to Why *)

open Format
open Mix_ast
open Mix_seq.X
open Mix_seq

type term = 
  | Tvar of string
  | Tconst of string
  | Tapp of string * term list

type why_stmt = 
  | Wvoid
  | Wassume of predicate
  | Wassert of predicate
  | Wseq of why_stmt * why_stmt
  | Wassign of string * term

type why_code = { why_pre : predicate option; why_code : why_stmt }

let index a = function
  | None -> a
  | Some i -> Tapp ("add_int", [a; Tvar ("!i" ^ i)])

let rec value_addr = function
  | PAself -> assert false (*TODO*)
  | PAconst s -> Tconst s
  | PAident s -> Tvar s
  | PAplus (a1, a2) -> Tapp ("add_int", [value_addr a1; value_addr a2])
  | PAuminus a -> Tapp ("neg_int", [value_addr a])

let value_op op = match op.pop_address, op.pop_index, op.pop_field with
  | Some a, i, None -> index (value_addr a) i
  | _ -> assert false (*TODO*)

let value_at op = Tapp ("access", [Tvar "!mem"; value_op op])

let interp_instr i op = match i with
  | Lda -> 
      Wassign ("a", value_at op)
  | Cmpa -> 
      Wassign ("cmp", Tapp ("sub_int",[Tvar "!a"; value_at op]))
  | Dec3 ->
      Wassign ("i3", Tapp ("sub_int", [Tvar "!i3"; Tconst "1"]))
  | Ent2 ->
      Wassign ("i2", value_op op)
  | Ent3 ->
      Wassign ("i3", value_op op)
  | Ent1 | Ent4 | Ent5 | Ent6
  | Dec1 | Dec2 | Dec4 | Dec5 | Dec6 -> 
      Wvoid (* TODO *)
  | Jmp | Jge | J3p | Halt -> 
      assert false 

let rec interp_stmt = function
  | Void -> Wvoid
  | Mix { node = PSassert p } -> Wassert p
  | Mix { node = PSinvariant _ } -> assert false
  | Mix { node = PSinstr (i, op) } -> interp_instr i op
  | Assume p -> Wassume p
  | Seq (s1, s2) -> Wseq (interp_stmt s1, interp_stmt s2)

let interp_seq c = { why_pre = c.seq_pre; why_code = interp_stmt c.seq_code }

let interp = List.map interp_seq

(* pretty-printing *)

let counter = ref 0

let rec term fmt = function
  | Tvar s | Tconst s -> fprintf fmt "%s" s
  | Tapp (f, l) -> fprintf fmt "@[(%s@ %a)@]" f (Pp.print_list Pp.space term) l

let rec print_why fmt = function
  | Wvoid -> fprintf fmt "void"
  | Wassume p -> fprintf fmt "[{} unit {%s}]" p
  | Wassert p -> fprintf fmt "(assert {%s}; void)" p
  | Wseq (s1, s2) -> fprintf fmt "%a;@ %a" print_why s1 print_why s2
  | Wassign (id, t) -> fprintf fmt "%s := %a" id term t

let print_why_code fmt c =
  incr counter;
  fprintf fmt "let seq%d () =@\n" !counter;
  begin match c.why_pre with
    | Some p -> fprintf fmt "  @[<hov 2>{ %s }@]@\n" (X.string_of_predicate p)
    | None -> ()
  end;
  fprintf fmt "  @[<hv>%a@]@\n@\n" print_why c.why_code


