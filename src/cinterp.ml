
(* Interpretation of C programs *)

open Format
open Ident
open Logic
open Types
open Cast
open Ptree

let parse_c_spec s =
  eprintf "parsing: %s@\n" s; flush stderr;
  let st = Stream.of_string s in
  Grammar.Entry.parse Parser.c_spec st

let interp_c_spec v an = 
  let (p,e,q) = match an with
    | None -> [], Effect.bottom, None
    | Some s -> parse_c_spec s
  in
  { pc_result_name = result; pc_result_type = PVpure v;
    pc_effect = e; pc_pre = p; pc_post = q }

let interp_decl = function
  | Ctypedecl (l, CDvar id, v) -> 
      Parameter (l, [id], PVref (PVpure v))
  | Ctypedecl (l, CDfun (id, bl, an), v) -> 
      let k = interp_c_spec v an in
      let bl = List.map (fun (v, id) -> (id, BindType (PVpure v))) bl in
      Parameter (l, [id], PVarrow (bl, k))
  | Ctypedecl _ -> 
      assert false

let interp = List.map interp_decl

