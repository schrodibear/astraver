
(*i $Id: ident.ml,v 1.15 2002-03-13 10:48:13 filliatr Exp $ i*)

type t = string

let create s = s

let string s = s

module Idset = Set.Make(struct type t = string let compare = compare end)
type set = Idset.t
module Idmap = Map.Make(struct type t = string let compare = compare end)

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
  if Idset.mem id s then next_away (next id) s else id

let print fmt s = Format.fprintf fmt "%s" s

(*s Possibly anonymous names *)

type name = Anonymous | Name of t

let print_name fmt = function
  | Name id -> print fmt id
  | Anonymous -> Format.fprintf fmt "_"

(*s Labelled identifiers. *)

let at_id id d = id ^ "@" ^ d

let is_at id =
  try let _ = String.index id '@' in true with Not_found -> false

let un_at id =
  try
    let n = String.index id '@' in
    String.sub id 0 n,
    String.sub id (succ n) (pred (String.length id - n))
  with Not_found ->
    invalid_arg "Ident.un_at"

let adr_id id = "adr_" ^ id

(*s Bound variables. *)

type bound = int

let bound =
  let n = ref 0 in
  fun () -> incr n; !n

let bound_id b = b

let print_bound fmt b = Format.fprintf fmt "#%d" b

(*s Pre-defined. *)

let anonymous = "_"

let t_add = "%add"
let t_sub = "%sub"
let t_mul = "%mul"
let t_div = "%div"
let t_neg = "%neg"
let t_sqrt = "%sqrt"

let t_lt = "%lt"
let t_le = "%le"
let t_gt = "%gt"
let t_ge = "%ge"
let t_eq = "%eq"
let t_neq = "%neq"

let t_eq_int = "%eq_int"
let t_eq_bool = "%eq_bool"
let t_eq_float = "%eq_float"
let t_eq_unit = "%eq_unit"

let t_neq_int = "%neq_int"
let t_neq_bool = "%neq_bool"
let t_neq_float = "%neq_float"
let t_neq_unit = "%neq_unit"

let t_zwf_zero = "zwf_zero"
let result = "result"
let default = "_"
let access = "access"
let store = "store"
let annot_bool = "annot_bool"
let well_founded = "well_founded"
let well_founded_induction = "well_founded_induction"

let p_and = "and"
let p_or = "or"
let p_not = "not"

let is_eq_neq id =
  id == t_eq || id == t_neq

let is_comparison id =
  id == t_lt || id == t_le || id == t_gt || id == t_ge

let is_relation id = 
  id == t_lt || id == t_le || id == t_gt || id == t_ge ||
  id == t_eq || id == t_neq

let is_arith id =
  id == t_add || id == t_sub || id == t_mul || id == t_div || id == t_neg

