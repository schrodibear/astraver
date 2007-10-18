(* ========================================================================= *)
(* Load theorem proving example code into OCaml toplevel.                    *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

#load "nums.cma";;                                     (* For Ocaml 3.06     *)
#load "camlp4o.cma";;                                  (* For quotations     *)

(* ------------------------------------------------------------------------- *)
(* Various small tweaks to OCAML's default state.                            *)
(* ------------------------------------------------------------------------- *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };; (* Up the stack size  *)
Format.set_margin 72;;                                 (* Reduce margins     *)
open Format;;                                          (* Open formatting    *)
open Num;;                                             (* Open bignums       *)
let imperative_assign = (:=);;                         (* Preserve this      *)

let print_num n = print_string(string_of_num n);;      (* Avoid range limit  *)
#install_printer print_num;;                           (* when printing nums *)

(* ------------------------------------------------------------------------- *)
(* Bind these special identifiers to something so we can just do "#use".     *)
(* ------------------------------------------------------------------------- *)

type dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Set up default quotation parsers for <<...>> and <<|...|>>.               *)
(* ------------------------------------------------------------------------- *)

let quotexpander s =
  if String.sub s 0 1 = "|" & String.sub s (String.length s - 1) 1 = "|" then
    "secondary_parser \""^
    (String.escaped (String.sub s 1 (String.length s - 2)))^"\""
  else "default_parser \""^(String.escaped s)^"\"";;

Quotation.add "" (Quotation.ExStr (fun x -> quotexpander));;

#use "atp.ml"
