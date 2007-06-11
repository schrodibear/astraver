
(* parsed trees *)

type instr = 
  | Jmp | Jge | J3p
  (* loading *)
  | Lda
  (* address transfer *)
  | Ent1 | Ent2 | Ent3 | Ent4 | Ent5 | Ent6
  | Dec1 | Dec2 | Dec3 | Dec4 | Dec5 | Dec6
  (* comparison *)
  | Cmpa
  | Halt

type paddress =
  | PAself
  | PAconst of string
  | PAident of string
  | PAplus of paddress * paddress
  | PAuminus of paddress

type pfield =
  | PFrange of string * string
  | PFident of string

type poperand =
  { pop_address : paddress option; 
    pop_index   : string option;
    pop_field   : pfield option; 
  }

type pstmt =
  | PSinvariant of string
  | PSassert of string
  | PSinstr of instr * poperand

type pseudo =
  | Equ_addr of string * paddress
  | Equ_field of string * pfield
  | Orig of string option * paddress

type pfile = pseudo list * (string option * pstmt) list
