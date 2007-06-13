
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

  let anon addr = 
    let lab = create () in { lab with lab_addr = addr }

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
  | IllegalCodeAddress of int

let report fmt = function
  | UnboundLabel s -> fprintf fmt "unbound label %s" s
  | IllegalCodeAddress n -> fprintf fmt "illegal address %d" n

exception Error of loc * error

let error loc s = raise (Error (loc, s))

(* symbol table *)

let labels_by_name = Hashtbl.create 97
let labels_by_addr = Hashtbl.create 97

let declare_label lab =
  Hashtbl.add labels_by_name lab.Label.lab_name lab;
  Hashtbl.add labels_by_addr lab.Label.lab_addr lab

let find_label_by_name loc id = 
  try Hashtbl.find labels_by_name id 
  with Not_found -> error loc (UnboundLabel id)

let find_label_by_addr loc a = 
  try Hashtbl.find labels_by_addr a
  with Not_found -> error loc (IllegalCodeAddress a)

(*
let equ = Hashtbl.create 17 
*)

(* Mixal: we resolve addresses *)

let step s = match s.node with
  | PSinvariant _ | PSassert _ -> 0
  | PSinstr _ -> 1

let eval_address self loc a =
  let rec addr = function
    | PAplus (a1, a2) -> addr a1 + addr a2
    | PAminus (a1, a2) -> addr a1 - addr a2
    | PAuminus a -> - (addr a)
    | PAident id -> let lab = find_label_by_name loc id in lab.Label.lab_addr
    | PAconst n -> int_of_string n
    | PAself -> self
  in
  match a.pop_address, a.pop_index, a.pop_field with
    | Some a, None, None -> addr a
    | None, _, _ | _, Some _, _ | _, _, Some _ -> assert false (*TODO*)

let address self loc = function
  | { pop_address = Some (PAident id); pop_index = None; pop_field = None } ->
      find_label_by_name loc id
  | a ->
      (* otherwise we eval the address and find the corresponding label *)
      find_label_by_addr loc (eval_address self loc a)

(* prev = previous instruction
   lab = label of current instruction *)
let interp_stmt self prev lab s = match s.node with
  | PSinvariant i -> 
      Ainvariant i
  | PSassert a -> 
      Aother (X.assert_stmt a)
  | PSinstr (Jmp, op) -> 
      Ajump (address self s.loc op)
  | PSinstr (J3p, op) -> 
      Acond (address self s.loc op, X.Assume "i3 > 0", X.Assume "i3 <= 0")
  | PSinstr (Jge, op) ->
      Acond (address self s.loc op, X.Assume "cmp >= 0", X.Assume "cmp < 0")
  | PSinstr (Halt, _) -> 
      Ahalt
  | PSinstr _ -> 
      Aother (X.Mix s)

let mixal (pseudo,asm) init =
  (* TODO pseudo *)  
  let self = ref 0 in
  (* 1. declare labels *)
  let asm =
    List.map
      (fun (lo, ps) -> 
	let l = match lo with 
	  | None -> Label.anon !self
	  | Some id -> Label.user id !self 
	in
	declare_label l;
	self := !self + step ps;
	l, ps)
    asm
  in
  (* 2. *)
  let rec map_instr prev = function
    | [] -> 
	[]
    | (l,i) :: r -> 
	(l, interp_stmt l.Label.lab_addr prev l i) :: map_instr (Some i) r
  in
  let asm = map_instr None asm in
  asm

let sequentialize asm init =
  let asm = mixal asm init in
  let init = find_label_by_name Lexing.dummy_pos init in
  transform asm init
