
open Stdlib
open Output_ast

module P = Pervasives
module S = Stdlib

let (@) : _ term -> _ term_hlist -> _ term_hlist = fun x xs -> Cons (x, xs)

let (@.) : _ term -> _ term -> _ term_hlist = fun x y -> Cons (x, Cons (y, Nil))

let (@$) : _ func -> _ term_hlist -> _ term = fun x y -> App (x, y)

let (@$.) : _ func -> _ term -> _ term = fun x y -> App (x, Cons (y, Nil))

let expr ?labels:(expr_labels=[]) node = { expr_labels; expr_node = node }

let (@:) labels ({ expr_labels } as e) = { e with expr_labels = P.(labels @ expr_labels) }

let (@@) : _ expr -> _ expr_hlist -> _ expr_hlist = fun x xs -> Cons (x, xs)

let (@@.) : _ expr -> _ expr -> _ expr_hlist = fun x y -> Cons (x, Cons (y, Nil))

let (@@$) : _ func -> _ expr_hlist -> _ expr = fun x y -> expr (App (x, y, None))

let (@@$.) : _ func -> _ expr -> _ expr = fun x y -> expr (App (x, Cons (y, Nil), None))

let (@@:) : _ expr -> _ why_type -> _ expr =
  fun e t ->
  match e.expr_node with
  | App (x, y, None) -> { e with expr_node = App (x, y, Some t) }
  | _ -> e

let (@@@) : _ logic_type -> _ ltype_hlist -> _ ltype_hlist = fun x xs -> Cons (x, xs)

let (@@@.) : _ logic_type -> _ logic_type -> _ ltype_hlist = fun x y -> Cons (x, Cons (y, Nil))

let (@@@$) : _ tconstr -> _ ltype_hlist -> _ logic_type = fun x y -> Type (x, y)

let (@@@$.) : _ tconstr -> _ logic_type -> _ logic_type = fun x y -> Type (x, Cons (y, Nil))

module type Enum_sig =
sig
  type range
  type b
  val ty : (range, b bit) integer
  val name : string
end

module Make_enum (I : Enum_sig) =
struct
  include I
  let theory = String.capitalize name
  let safe_module = "Safe_" ^ name
  let unsafe_module = "Unsafe_" ^ name
  type t = (I.range, I.b bit) integer
  let bin_t op flag t1 t2 = B_bint_op (op, I.ty, flag) @$ t1 @. t2
  let un_t op flag t = U_bint_op (op, I.ty, flag) @$. t
  let (+) = bin_t `Add false
  let (+%) = bin_t `Add true
  let (-) = bin_t `Sub false
  let (-%) = bin_t `Sub true
  let ( * ) = bin_t `Mul false
  let ( *%) = bin_t `Mul true
  let (/) = bin_t `Div false
  let (/%) = bin_t `Div true
  let (%) = bin_t `Mod false
  let (%%) = bin_t `Mod true
  let of_int t = Of_int I.ty @$. t
  let to_int t = To_int I.ty @$. t
  let bin_p pred t1 t2 : pred = App (B_num_pred (pred, Integral I.ty), t1 @. t2)
  let (>) = bin_p `Gt
  let (>=) = bin_p `Ge
  let (<) = bin_p `Lt
  let (<=) = bin_p `Le
  let (=) = bin_p `Eq
  let (<>) = bin_p `Ne
end

module Enum (I : sig type range' type b' end) =
struct
  type range = I.range'
  type b = I.b'
  let ty = failwith "The dummy functor Enum should never be applied"
  let name = "enum"
end

module type Enum =
sig
  type range
  type b
  include module type of Make_enum (Enum (struct type range' = range type b' = b end))
  with type range := range and type b := b
end

module type Int_sig =
sig
  type r
  type b
  val ty : (r range, b bit) integer
  val name : string
end

module Make_int (I : Int_sig) =
struct
  type r = I.r
  include Make_enum
      (struct
        include I
        type range = r Output_ast.range
      end)
  let bit_theory = "Bit" ^ name
  let safe_bit_module = "Safe_bit_" ^ name
  let unsafe_bit_module = "Unsafe_bit_" ^ name
  let bin_bop op t1 t2 = B_bint_bop (op, I.ty) @$ t1 @. t2
  let un_bop op t = U_bint_bop (op, I.ty) @$. t
  let (&) = bin_bop `And
  let (||) = bin_bop `Or
  let xor = bin_bop `Xor
  let (>>) = bin_bop `Lsr
  let (>>>) = bin_bop `Asr
  let (~~) = un_bop `Compl
  let (<<) (*>>)*) t1 t2 = Lsl_bint (I.ty, false) @$ t1 @. t2
  let (<<%) t1 t2 = Lsl_bint (I.ty, true) @$ t1 @. t2
end

module Int (I : sig type r' type b' end) =
struct
  type r = I.r'
  type b = I.b'
  let ty = failwith "The dummy functor Int should never be applied"
  let name = "int"
end

module type Int =
sig
  type r
  type b
  include module type of Make_int (Int (struct type r' = r type b' = b end)) with type r := r and type b := b
end

module Int8 =
  Make_int
    (struct
      type r = signed
      type b = _8
      let ty : _ integer = Int (Signed, X8)
      let name = "int8"
    end)

module Uint8 =
  Make_int
    (struct
      type r = unsigned
      type b = _8
      let ty : _ integer = Int (Unsigned, X8)
      let name = "uint8"
    end)

module Int16 =
  Make_int
    (struct
      type r = signed
      type b = _16
      let ty : _ integer = Int (Signed, X16)
      let name = "int16"
    end)

module Uint16 =
  Make_int
    (struct
      type r = unsigned
      type b = _16
      let ty : _ integer = Int (Unsigned, X16)
      let name = "uint16"
    end)

module Int32 =
  Make_int
    (struct
      type r = signed
      type b = _32
      let ty : _ integer = Int (Signed, X32)
      let name = "int32"
    end)

module Uint32 =
  Make_int
    (struct
      type r = unsigned
      type b = _32
      let ty : _ integer = Int (Unsigned, X32)
      let name = "uint32"
    end)

module Int64 =
  Make_int
    (struct
      type r = signed
      type b = _64
      let ty : _ integer = Int (Signed, X64)
      let name = "int64"
    end)

module Uint64 =
  Make_int
    (struct
      type r = unsigned
      type b = _64
      let ty : _ integer = Int (Unsigned, X64)
      let name = "uint64"
    end)

let module_of_int_ty : type r b. (r range, b bit) integer -> (module Int with type r = r and type b = b) =
  function
  | Int (Signed, X8) -> (module Int8)
  | Int (Unsigned, X8) -> (module Uint8)
  | Int (Signed, X16) -> (module Int16)
  | Int (Unsigned, X16) -> (module Uint16)
  | Int (Signed, X32) -> (module Int32)
  | Int (Unsigned, X32) -> (module Uint32)
  | Int (Signed, X64) -> (module Int64)
  | Int (Unsigned, X64) -> (module Uint64)

let int n = Const (Int (string_of_int n))

let num n = Const (Int (Num.string_of_num n))

let var_lt s : _ logic_type = Var s @@@$ Nil

let bool_lt = Bool @@@$ Nil

let void_lt = Void @@@$ Nil

let lt s ~from:(name, import) = User (name, import, s)

let var_t s : _ term = Var s

let positioned_t l_pos ?behavior:(l_behavior = "default") ?kind:l_kind t =
  (Labeled ({ l_kind; l_behavior; l_pos }, t) : _ term)

let located_t l = positioned_t (Position.of_loc l)

let positioned'_t l = positioned_t (Position.of_pos l)

let bin_t op t1 t2 = B_int_op op @$ t1 @. t2

let (+) t1 t2 =
  match t1, t2 with
  | Const Int "0", _ -> t2
  | _, Const Int "0" -> t1
  | _ -> bin_t `Add t1 t2

let (-) t1 t2 =
  match t1, t2 with
  | Const Int "0", _ -> t2
  | _, Const Int "0" -> t1
  | _ -> bin_t `Sub t1 t2

let ( * ) t1 t2 =
  match t1, t2 with
  | Const Int "0", _
  | _, Const Int "0" -> int 0
  | Const Int "1", _ -> t2
  | _, Const Int "1" -> t1
  | _ -> bin_t `Mul t1 t2

let (/) t1 t2 =
  match t1, t2 with
  | _, Const Int "0" -> failwith "/: division by zero in integer term"
  | Const Int "0", _ -> int 0
  | _, Const Int "1" -> t1
  | _ -> bin_t `Div t1 t2

let (%) t1 t2 =
  match t1, t2 with
  | _, Const Int "0" -> failwith "/: division by zero in integer term"
  | Const Int "0", _
  | _, Const Int "1" -> int 0
  | _ -> bin_t `Mod t1 t2

let (-~)  =
  function
  | Const Int "0" -> int 0
  | t -> U_int_op `Neg @$. t

let (!) v = Deref v

let at_t v ~lab = Deref_at (v, lab)

let if_t cond ~then_ ~else_ = If (cond, then_, else_)

let let_t v ~equal ~in_ = Let (v, equal, in_)

let f s ~from:(name, import) = (User (name, import, s) : _ func)

let bin_p op t1 t2 : pred = App (B_num_pred (op, Integral Integer), t1 @. t2)

let (>) = bin_p `Gt
let (>=) = bin_p `Ge
let (<) = bin_p `Lt
let (<=) = bin_p `Le

let (=) t1 t2 = Poly `Eq @$ t1 @. t2
let (<>) t1 t2 = Poly `Neq @$ t1 @. t2

let rec unlabel_p : pred -> pred =
  function
  | Labeled (_, p) -> unlabel_p p
  | p -> p

let positioned_p l_pos ?behavior:(l_behavior = "default") ?kind:l_kind p =
  (Labeled ({ l_kind; l_behavior; l_pos }, p) : pred)

let located_p = S.(positioned_p % Position.of_loc)

let positioned'_p  = S.(positioned_p % Position.of_pos)

let is_not_true p =
  match unlabel_p p with
  | True -> false
  | _ -> true

let not p =
  match unlabel_p p with
  | True -> False
  | False -> True
  | _ -> Not p

let (&&) p1 p2 =
  match unlabel_p p1, unlabel_p p2 with
  | True, _ -> True
  | _, True -> True
  | False, _ -> p2
  | _, False -> p1
  | _, _ -> Or (p1, p2)

let (||) p1 p2 =
  match unlabel_p p1, unlabel_p p2 with
  | True, _ -> p2
  | _, True -> p1
  | False, _ -> False
  | _, False -> False
  | _, _ -> And (p1, p2)

let rec conj =
  function
  | [] -> True
  | p :: ps -> p && conj ps

let rec disj =
  function
  | [] -> False
  | p :: ps -> p || disj ps

let rec forall vs ?(trigs=[]) p =
  match vs with
  | [] -> p
  | [v, ty] -> Forall (v, ty, trigs, p)
  | (v, ty) :: vs -> Forall (v, ty, [], forall vs ~trigs p)

let impl p1 p2 =
  match unlabel_p p1, unlabel_p p2 with
  | True, _ -> p2
  | _, True -> True
  | False, _ -> True
  | _, False -> Not p1
  | _, _ -> Impl (p1, p2)

let rec impls conclu =
  function
  | [] -> conclu
  | p :: ps -> Impl (p, impls conclu ps)

let iff p1 p2 =
  match unlabel_p p1, unlabel_p p2 with
  | True, _ -> p2
  | _, True -> p1
  | False, _ -> not p2
  | _, False -> not p1
  | _, _ -> Iff (p1, p2)

let base_wt t = Base_type (t @@@$ Nil)

let integer_wt = P.(base_wt @@ Numeric (Integral Integer))

let bool_wt = base_wt Bool

let unit_wt = base_wt Void

let positioned_e l_pos ?behavior:(l_behavior = "default") ?kind:l_kind e =
  { e with expr_node = Labeled ({ l_kind; l_behavior; l_pos }, e) }

let located_e l = positioned_e (Position.of_loc l)

let positioned'_e l = positioned_e (Position.of_pos l)

let var_e v = expr (Var v)

let void_e = expr Void

let or_e e1 e2 =
  match e1.expr_node, e2.expr_node with
  | Cte (Bool true), _ -> e1
  | _, Cte (Bool true) -> e2
  | Cte (Bool false), _ -> e2
  | _, Cte (Bool false) -> e1
  | _, _ -> expr (Or (e1, e2))

let and_e e1 e2 =
  match e1.expr_node, e2.expr_node with
  | Cte (Bool true), _ -> e2
  | _, Cte (Bool true)  -> e1
  | Cte (Bool false), _ -> e1
  | _, Cte (Bool false) -> e2
  | _, _ -> expr (And (e1, e2))

let while_e cond ~inv ~var e =
  let body =
    match e.expr_node with
    | Block l -> l
    | _ -> [e]
  in
  expr (While (cond, inv, var, body))

let block_e ?(labs=[]) =
  function
  | [] -> labs @: void_e
  | [e] -> labs @: e
  | l -> labs @: expr (Block l)

let rec (^@) e1 e2 =
  match e1.expr_labels, e1.expr_node, e2.expr_labels, e2.expr_node with
  | labs1, Void, _, _ -> labs1 @: e2
  | _, _, [], Void -> e1
  | labs1, Block [], _, _ -> (labs1 @: void_e) ^@ e2
  | _, _, labs2, Block [] -> e1 ^@ labs2 @: void_e
  | labs1, Block [e1], _, _ -> (labs1 @: e1) ^@ e2
  | _, _, labs2, Block [e2] -> e1 ^@ labs2 @: e2
  | labs, Block l1, _, _ ->
    block_e ~labs (append l1 [e2])
  | labs, _, labs2, Block (e2 :: e2s) ->
    block_e ~labs (append [e1] ((labs2 @: e2) :: e2s))
  | labs, _, _, _ ->
    block_e ~labs [{ e1 with expr_labels = [] }; e2]

and append l1 l2 =
  match l1 with
  | [] -> l2
  | [e1] ->
    begin match l2 with
    | [] -> [e1]
    | e2 :: e2s ->
      match e1 ^@ e2 with
      | { expr_labels; expr_node = Block (e1 :: e1s) } ->
        append ((expr_labels @: e1) :: e1s) e2s
      | e ->
        append [e] e2s
    end
  | e1 :: e1s -> e1 :: append e1s l2

let id { why_id } = why_id
