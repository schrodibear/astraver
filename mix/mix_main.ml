
module X = struct
  module Label = struct
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
    let create = let r = ref 0 in fun () -> incr r; "L" ^ string_of_int !r
    let to_string l = l
  end

  type predicate = string
    
  let ptrue = "true"
  let string_of_predicate p = p

  type statement = string
    
  let void_stmt = "void"
  let append_stmt s1 s2 = s1 ^ "; " ^ s2
  let assert_stmt p = "assert " ^ p
  let string_of_stmt s = s

end

module Seq = Mix_cfg.Make(X)

let asm =
  let c = open_in Sys.argv.(1) in
  let lb = Lexing.from_channel c in
  let asm = Mix_parser.file Mix_lexer.token lb in
  close_in c;
  asm

let cl = Seq.transform asm Sys.argv.(2)



