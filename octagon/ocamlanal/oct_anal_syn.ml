(* oct_anal_syn.ml
   Concrete syntax of the toy language for the example analyzer.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
*)

(* comparison operators <, <=, >, >=, =, != *)
type comp = LESS | LESSEQ | GREATER | GREATEREQ | EQ | NOTEQ

(* program *)
type prog = string * block

(* instructions *)
and inst =
    ASSIGN of string*iexpr
  | ASSERT of bexpr
  | IF     of bexpr*block
  | IF2    of bexpr*block*block
  | LOOP   of bexpr*block

(* in an instruction block, the first int is the offset before the first
   instruction of the block; then each instruction is packed with the offset
   at the end of the instruction 
*)
and block = int*((inst*int) list)

(* boolean expressions *)
and bexpr =
    AND  of bexpr*bexpr
  | OR   of bexpr*bexpr
  | COMP of comp*iexpr*iexpr
  | NOT  of bexpr
  | TRUE
  | FALSE
  | BRAND   (* random boolean *)

(* numerical expressions *)
and iexpr =
    VAR of string
  | RAND          (* random integer *)
  | CST of float
  | PLUS of iexpr*iexpr
  | MINUS of iexpr*iexpr
  | TIMES of iexpr*iexpr


(* Shared variables *)
(* **************** *)

(* index ofthe current line *)
let cur_line = ref 1

(* this stack stores the ofsset (character from begining of file) where each 
   line begins *)
let line_offsets = ref [0,1]

(* offset where the comment started => used to detect unterminated comment *)
let start_of_comment = ref 0

(* there is some funky things in order to get the offset where an instruction
   begins or ends when there is no semicolon to guide us:
   mainly, -1 offset are put when construction the block
   then, when the block is linked as leafs of higher-order constructs such
   as if/then/else, while/do/done, begin/end, or program/endprogram, the
   offsets of the keywords are used to update the offsets values in a block to
   correct values
*)

(* change the offset before the first instruction of block b *)
let set_start_block b pos = match b with
  (-1,a) -> (pos,a)
| b      -> b

(* change the offset after the last instruction of block b *)
let rec set_end_block b pos =
  let rec toto = function
      [] -> []
    | (a,-1)::[] -> (set_end_inst a pos,pos)::[]
    | (a,b)::[] -> (a,b)::[]
    | a::b -> a::(toto b)
  in match b with (p,bb) -> (p,toto bb)

and set_end_inst b pos = match b with
  IF(a,b   ) -> IF (a,  set_end_block b pos)
| IF2(a,b,c) -> IF2(a,b,set_end_block c pos)
| a          -> a

exception Unterminated_comment of int
