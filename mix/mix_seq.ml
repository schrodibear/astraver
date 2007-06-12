
(* Turn a MIX program into a set of sequential MIX programs *)

open Format
open Mix_ast

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

  let user id addr = 
    { lab_name = id; lab_user = true; lab_addr = addr }

  let to_string l = l.lab_name

end

module X = struct

  module Label = Label

  type predicate = string
    
  let ptrue = "true"
  let string_of_predicate p = p

  type statement = 
    | Void
    | Mix of pstmt
    | Assume of predicate
    | Seq of statement * statement
    
  let void_stmt = Void
  let append_stmt s1 s2 = Seq (s1, s2)
  let assert_stmt p = Mix { node = PSassert p; loc = Lexing.dummy_pos }

  let rec string_of_stmt = function
    | Void -> "void"
    | Mix { node = PSassert p } -> "assert ... "
    | Mix _ -> "<mix>"
    | Assume s -> "assume " ^ s
    | Seq (s1, s2) -> string_of_stmt s1 ^ "; " ^ string_of_stmt s2

end

include Mix_cfg.Make(X)

(* error reporting *)

type error = 
  | UnboundLabel of string

let report fmt = function
  | UnboundLabel s -> fprintf fmt "unbound label %s" s

exception Error of loc * error

let error loc s = raise (Error (loc, s))

(* Mixal: we resolve addresses *)

let labels = Hashtbl.create 97

let step s = match s.node with
  | PSinvariant _ | PSassert _ -> 0
  | PSinstr _ -> 1

let find_label loc id = 
  try Hashtbl.find labels id 
  with Not_found -> error loc (UnboundLabel id)

let address loc = function
  | { pop_address = Some (PAident id); pop_index = None; pop_field = None } ->
      find_label loc id
  | _ ->
      assert false (*TODO*)

(* prev = previous instruction
   lab = label of current instruction *)
let interp_stmt prev lab s = match s.node with
  | PSinvariant i -> 
      Ainvariant i
  | PSassert a -> 
      Aother (X.assert_stmt a)
  | PSinstr (Jmp, op) -> 
      Ajump (address s.loc op)
  | PSinstr (J3p, op) -> 
      Acond (address s.loc op, X.Assume "i3 > 0", X.Assume "i3 <= 0")
  | PSinstr (Jge, op) ->
      Acond (address s.loc op, X.Assume "cmp >= 0", X.Assume "cmp < 0")
(***
      if lab <> None then failwith "unsupported test with label";
      let tt,tf = match prev with
	| Some (PSinstr (Cmpa, _)) -> 
	    X.Assume "cond true", X.Assume "cond false"
	| _ -> 
	    failwith "unsupported test"
      in
      Acond (address op, tt, tf)
***)
  | PSinstr (Halt, _) -> 
      Ahalt
  | PSinstr _ -> 
      Aother (X.Mix s)

let mixal (pseudo,asm) init =
  (* TODO pseudo *)  
  let addr = ref 0 in
  (* 1. declare labels *)
  let asm =
    List.map
      (fun (lo, ps) -> 
	let l = match lo with 
	  | None -> 
	      None
	  | Some id -> 
	      let l = Label.user id !addr in
	      Hashtbl.add labels id l;
	      Some l
	in
	addr := !addr + step ps;
	l, ps)
    asm
  in
  (* 2. *)
  let rec map_instr prev = function
    | [] -> []
    | (l,i) :: r -> (l, interp_stmt prev l i) :: map_instr (Some i) r
  in
  map_instr None asm

let sequentialize asm init =
  let asm = mixal asm init in
  let init = find_label Lexing.dummy_pos init in
  transform asm init
