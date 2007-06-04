
(* parsed trees *)

type pstmt = 
  | PSinvariant of string
  | PSjump of string
  | PScond of string
  | PShalt
  | PSother of string

type pfile = (string option * pstmt) list
