
module Label = struct

  type t = 
    { lab_name : string; 
      lab_user : bool;
      lab_addr : int;
    }

  let equal = (=)

  let hash = Hashtbl.hash

  let create = 
    let r = ref 0 in 
    fun () -> 
      incr r; 
      { lab_name = "L" ^ string_of_int !r;
	lab_user = false;
	lab_addr = 0 }

  let to_string l = l.lab_name

end

module X = struct

  module Label = Label

  type predicate = string
    
  let ptrue = "true"
  let string_of_predicate p = p

  type statement = string
    
  let void_stmt = "void"
  let append_stmt s1 s2 = s1 ^ "; " ^ s2
  let assert_stmt p = "assert " ^ p
  let string_of_stmt s = s

end

include  Mix_cfg.Make(X)


(***
let interp_stmt = function
  | PSinvariant i -> Seq.Ainvariant i
  | PSjump l -> Seq.Ajump l
  | PScond l -> Seq.Acond (l, "cond true", "cond false")
  | PShalt -> Seq.Ahalt
  | PSother s -> Seq.Aother s

let asm = List.map (fun (l,s) -> (l, interp_stmt s)) asm
let asm = []
***)

let interp asm init =
  [] (*TODO*)
