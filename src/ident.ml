
type t = string

let create s = s

let string s = s

type name = Anonymous | Name of t

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

(*s Pre-defined. *)

let t_add = "add"
let t_sub = "sub"
let t_mul = "mul"
let t_div = "div"
let t_neg = "neg"

let t_lt = "lt"
let t_le = "le"
let t_gt = "gt"
let t_ge = "ge"
let t_eq = "eq"
let t_noteq = "noteq"

let t_zwf_zero = "zwf_zero"
let result = "result"
let default = "_"

let p_and = "and"
let p_or = "or"
let p_not = "not"
