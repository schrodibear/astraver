
(*i $Id: ident.ml,v 1.18 2002-04-29 08:47:36 filliatr Exp $ i*)

type t = { stamp : int; name : string }

let create s = { stamp = 0; name = s }

let string s = s.name

module I = struct type t_ = t type t = t_ let compare = compare end

module Idset = Set.Make(I)
type set = Idset.t

module Idmap = Map.Make(I)
type 'a map = 'a Idmap.t

let is_index s = 
  let n = String.length s in
  (n > 0) && (match s.[n-1] with '0'..'9' -> true | _ -> false)

let rec next id =
  if not (is_index id) then
    id ^ "0"
  else
    let n = String.length id in
    match id.[n - 1] with
      | '0'..'8' as c -> 
	  let id' = String.copy id in 
	  id'.[n - 1] <- Char.chr (Char.code c + 1); 
	  id'
      | '9' ->
	  let id' = String.sub id 0 (n - 1) in
	  (next (if is_index id' then id' else id' ^ "0")) ^ "0"
      | _ -> 
	  assert false

let rec next_away id s =
  if Idset.mem id s then next_away (create (next id.name)) s else id

let print fmt s = Format.fprintf fmt "%s" s.name

(*s Possibly anonymous names *)

type name = Anonymous | Name of t

let print_name fmt = function
  | Name id -> print fmt id
  | Anonymous -> Format.fprintf fmt "_"

(*s Labelled identifiers. *)

let at_id id d = create (id.name ^ "@" ^ d)

let is_at id =
  try let _ = String.index id.name '@' in true with Not_found -> false

let un_at id =
  let s = id.name in 
  try
    let n = String.index s '@' in
    create (String.sub s 0 n),
    String.sub s (succ n) (pred (String.length s - n))
  with Not_found ->
    invalid_arg "Ident.un_at"

let adr_id id = create ("adr_" ^ id.name)

(*s Bound variables. *)

let bound =
  let n = ref 0 in
  fun s -> incr n; { stamp = !n; name = s.name }

(*s Pre-defined. *)

let anonymous = create "_"

let t_add = create "%add"
let t_sub = create "%sub"
let t_mul = create "%mul"
let t_div = create "%div"
let t_mod = create "%mod"
let t_neg = create "%neg"
let t_sqrt = create "%sqrt"

let t_lt = create "%lt"
let t_le = create "%le"
let t_gt = create "%gt"
let t_ge = create "%ge"
let t_eq = create "%eq"
let t_neq = create "%neq"

let t_eq_int = create "%eq_int"
let t_eq_bool = create "%eq_bool"
let t_eq_float = create "%eq_float"
let t_eq_unit = create "%eq_unit"

let t_neq_int = create "%neq_int"
let t_neq_bool = create "%neq_bool"
let t_neq_float = create "%neq_float"
let t_neq_unit = create "%neq_unit"

let t_zwf_zero = create "zwf_zero"
let result = create "result"
let default = create "_"
let access = create "access"
let store = create "store"
let annot_bool = create "annot_bool"
let well_founded = create "well_founded"
let well_founded_induction = create "well_founded_induction"

let p_and = create "and"
let p_or = create "or"
let p_not = create "not"

let is_eq_neq id =
  id == t_eq || id == t_neq

let is_comparison id =
  id == t_lt || id == t_le || id == t_gt || id == t_ge

let is_relation id = 
  id == t_lt || id == t_le || id == t_gt || id == t_ge ||
  id == t_eq || id == t_neq

let is_arith id =
  id == t_add || id == t_sub || id == t_mul || id == t_div || id == t_neg

