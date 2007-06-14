
(* parsed trees *)

type loc = Lexing.position

type 'a located = { node : 'a; loc : loc }

type register = A | X | I1 | I2 | I3 | I4 | I5 | I6

type instr = 
  (* loading *)
  | Ld of register
  (* storing *)
  | St of register | Stj | Stz
  (* arithmetic *)
  | Add | Sub | Mul | Div
  (* address transfer *)
  | Ent of register
  | Inc of register
  | Dec of register
  (* comparison *)
  | Cmp of register
  (* jump *)
  | Jmp | Jsj 
  | Jl | Je | Jg | Jge | Jne | Jle
  | Jn of register | Jz of register | Jp of register
  | Jnn of register | Jnz of register | Jnp of register
  (* other *)
  | Nop
  | Hlt

type paddress =
  | PAself
  | PAconst of string
  | PAident of string
  | PAplus of paddress * paddress
  | PAminus of paddress * paddress
  | PAuminus of paddress

type pfield =
  | PFrange of string * string
  | PFident of string

type poperand =
  { pop_address : paddress option; 
    pop_index   : string option;
    pop_field   : pfield option; 
  }

type pstmt = pstmt_node located

and pstmt_node =
  | PSinvariant of string
  | PSassert of string
  | PSinstr of instr * poperand

type pseudo = pseudo_node located

and pseudo_node =
  | Equ_addr of string * paddress
  | Equ_field of string * pfield
  | Orig of string option * paddress
  | Verbatim of string

type pfile = pseudo list * (string option * pstmt) list
