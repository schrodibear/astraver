(* explanations *)

let program_locs = Hashtbl.create 17

(*
let read_in_file f l b e = 
  let ch = open_in f in
  for i = 2 to l do
    ignore (input_line ch)
  done;
  for i = 1 to b do
    ignore (input_char ch)
  done;
  let buf = Buffer.create 17 in
  for i = b to e-1 do
    Buffer.add_char buf (input_char ch)
  done;
  Buffer.contents buf
*)
 
open Format
open Logic
open Logic_decl

  
let raw_loc ?(pref="") fmt (f,l,b,e) =
  fprintf fmt "%sfile = \"%s\"@\n" pref f;
  fprintf fmt "%sline = %d@\n" pref l;
  fprintf fmt "%sbegin = %d@\n" pref b;
  fprintf fmt "%send = %d@\n" pref e
 
let print_formula fmt s =
  if String.length s > 0 then
    fprintf fmt "formula = \"%s\"@\n" s

let print_kind fmt (loc,k) =
  (* 
     Option_misc.iter (fun lab ->  fprintf fmt "label = %s@\n" lab) labopt; 
  *)
  raw_loc fmt loc;
  match k with
    | EKOther s -> fprintf fmt "kind = Other@\ntext = \"%s\"@\n" s
    | EKAbsurd -> fprintf fmt "kind = Absurd@\n"
    | EKAssert -> fprintf fmt "kind = Assert@\n"
    | EKPre s -> fprintf fmt "kind = Pre@\ntext = \"%s\"@\n" s
    | EKPost -> fprintf fmt "kind = Post@\n"
    | EKWfRel -> fprintf fmt "kind = WfRel@\n"
    | EKVarDecr -> fprintf fmt "kind = VarDecr@\n" 
    | EKLoopInvInit s -> 
	fprintf fmt "kind = LoopInvInit@\n";
	print_formula fmt s
    | EKLoopInvPreserv s -> 
	fprintf fmt "kind = LoopInvPreserv@\n";
	print_formula fmt s
    | EKLemma -> fprintf fmt "kind = Lemma@\n"


let print fmt ((*loc,*)e) = print_kind fmt (e.vc_loc,e.vc_kind)

