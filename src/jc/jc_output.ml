
open Stdlib
open Common
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
  type bound
  val ty : bound bounded integer
  val name : string
end

module Make_enum (I : Enum_sig) =
struct
  include I
  let theory = String.capitalize name
  let safe_module = "Safe_" ^ name
  let unsafe_module = "Unsafe_" ^ name
  type t = I.bound bounded integer
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

module Enum (I : sig type bound' end) =
struct
  type bound = I.bound'
  let ty = failwith "The dummy functor Enum should never be applied"
  let name = "enum"
end

module type Enum =
sig
  type bound
  include module type of Make_enum (Enum (struct type bound' = bound end))
  with type bound := bound
end

module type Int_sig =
sig
  type r
  type b
  val ty : (r repr, b bit) xintx bounded integer
  val name : string
end

module Make_int (I : Int_sig) =
struct
  type r = I.r
  type b = I.b
  include Make_enum
      (struct
        include I
        type bound = (I.r repr, I.b bit) xintx
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

let module_of_int_ty : type r b. (r repr, b bit) xintx bounded integer -> (module Int with type r = r and type b = b) =
  function
  | Int (Signed, X8) -> (module Int8)
  | Int (Unsigned, X8) -> (module Uint8)
  | Int (Signed, X16) -> (module Int16)
  | Int (Unsigned, X16) -> (module Uint16)
  | Int (Signed, X32) -> (module Int32)
  | Int (Unsigned, X32) -> (module Uint32)
  | Int (Signed, X64) -> (module Int64)
  | Int (Unsigned, X64) -> (module Uint64)

let int_t n = Const (Int (string_of_int n))

let num_t n = Const (Int (Num.string_of_num n))

let void_t = Const Void

let real_t s = Const (Real s)

let bool_t b = Const (Bool b)

let var_lt s : _ logic_type = Var s @@@$ Nil

let bool_lt = Bool @@@$ Nil

let void_lt = Void @@@$ Nil

let integer_lt = Numeric (Integral Integer) @@@$ Nil

let int_lt i = Numeric (Integral i) @@@$ Nil

let enum_lt s = Numeric (Integral (Enum s)) @@@$ Nil

let real_lt = Numeric (Real Real) @@@$ Nil

let single_lt = Numeric (Real (Float Single)) @@@$ Nil

let double_lt = Numeric (Real (Float Double)) @@@$ Nil

let var_lt v = Var v @@@$ Nil

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
  | _, Const Int "0" -> int_t 0
  | Const Int "1", _ -> t2
  | _, Const Int "1" -> t1
  | _ -> bin_t `Mul t1 t2

let (/) t1 t2 =
  match t1, t2 with
  | _, Const Int "0" -> failwith "/: division by zero in integer term"
  | Const Int "0", _ -> int_t 0
  | _, Const Int "1" -> t1
  | _ -> bin_t `Div t1 t2

let (%) t1 t2 =
  match t1, t2 with
  | _, Const Int "0" -> failwith "/: division by zero in integer term"
  | Const Int "0", _
  | _, Const Int "1" -> int_t 0
  | _ -> bin_t `Mod t1 t2

let (-~)  =
  function
  | Const Int "0" -> int_t 0
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

let (=) t1 t2 : pred = App (Poly `Eq, t1 @. t2)
let (<>) t1 t2 : pred = App (Poly `Neq, t1 @. t2)

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

let jc_lt = lt ~from:Name.Theory.jessie

let jc_f = f ~from:Name.Theory.jessie

let jc_v = f ~from:Name.Module.jessie

let select mem p =
  jc_f "select" @$ mem @. p

open Name

let ( **>) fi = select (var_t (field_memory_name fi))

let select_commited pc = select (var_t (committed_name pc))

let typeof tt p = jc_f "typeof" @$ tt @. p

let typeeq tt p st = typeof tt p = var_t (Name.tag st)

let (<:) t1 t2 : pred = App (jc_f "subtag", t1 @. t2)

let instanceof tt p st : pred = App (jc_f "instanceof", tt @ p @. var_t (Name.tag st))

let alloc_table ?r ac =
  var_t (Option.map_default r ~default:(Name.Generic.alloc_table ac) ~f:(fun r -> Name.alloc_table (ac, r)))

let offset_min ac ?r p =
  jc_f "offset_min" @$ alloc_table ?r ac @. p

let offset_max ac ?r p =
  jc_f "offset_max" @$ alloc_table ?r ac @. p

let int_of_tag st = jc_f "int_of_tag" @$. var_t (Name.tag st)

let rec string_of_ty : type a. a ty -> string =
  function
  | (Numeric (Integral Integer) : a ty) -> "integer"
  | Numeric (Integral (Int (r, b))) -> string_of_any_enum (Env.Int (r, b))
  | Numeric (Integral (Enum s)) -> string_of_any_enum (Env.Enum s)
  | Numeric (Real Real) -> "real"
  | Numeric (Real (Float Single)) -> "single"
  | Numeric (Real (Float Double)) -> "double"
  | Bool -> "bool"
  | Void -> "void"
  | Ref r -> "ref " ^ string_of_ty r
  | Arrow (t1, t2) -> string_of_ty t1 ^ " -> " ^ string_of_ty t2
  | Ex -> "\"existential, i.e. some distinct type\""

type (_, _) eq = Eq : ('a, 'a) eq

let rec eq_ty : type a b. a ty -> b ty -> (a, b) eq = fun a b ->
  match a, b with
  | Numeric (Integral Integer),               Numeric (Integral Integer) -> Eq
  | Numeric (Integral (Int (Signed, X8))),    Numeric (Integral (Int (Signed, X8))) -> Eq
  | Numeric (Integral (Int (Unsigned, X8))),  Numeric (Integral (Int (Unsigned, X8))) -> Eq
  | Numeric (Integral (Int (Signed, X16))),   Numeric (Integral (Int (Signed, X16))) -> Eq
  | Numeric (Integral (Int (Unsigned, X16))), Numeric (Integral (Int (Unsigned, X16))) -> Eq
  | Numeric (Integral (Int (Signed, X32))),   Numeric (Integral (Int (Signed, X32))) -> Eq
  | Numeric (Integral (Int (Unsigned, X32))), Numeric (Integral (Int (Unsigned, X32))) -> Eq
  | Numeric (Integral (Int (Signed, X64))),   Numeric (Integral (Int (Signed, X64))) -> Eq
  | Numeric (Integral (Int (Unsigned, X64))), Numeric (Integral (Int (Unsigned, X64))) -> Eq
  | Numeric (Integral (Enum s)),              Numeric (Integral (Enum s')) when P.(s = s') -> Eq
  | Numeric (Integral (Enum s)),              Numeric (Integral (Enum s')) ->
    failwith ("Enum mismatch in Why3ML output: expected: `" ^ s ^ "', got: `" ^ s' ^ "'")
  | Numeric (Real Real),                      Numeric (Real Real) -> Eq
  | Numeric (Real (Float Single)),            Numeric (Real (Float Single)) -> Eq
  | Numeric (Real (Float Double)),            Numeric (Real (Float Double)) -> Eq
  | Bool,                                     Bool -> Eq
  | Void,                                     Void -> Eq
  | Ref ty,                                   Ref ty' -> let Eq = eq_ty ty ty' in Eq
  | Arrow (t1, t2),                           Arrow (t1', t2') ->
    let Eq = eq_ty t1 t1' in
    let Eq = eq_ty t2 t2' in
    Eq
  | _ ->
    failwith ("Type mismatch in Why3ML output: expected: `" ^ string_of_ty a ^ "', got: `" ^ string_of_ty b ^ "'")

let ty (type a) (type b) : (a, b) ty_opt -> _ =
  function
  | Ty _ as t -> t
  | Any ->
    failwith "Instantiated polymorphic (`some' vs. `any') type was expected when typing monomorphic AST node"

module Ty =
struct
  let integer : _ ty = Numeric (Integral Integer)
  let int i : _ ty = Numeric (Integral i)
  let float r : _ ty = Numeric (Real r)
  let real : _ ty = Numeric (Real Real)
end

type 'a poly_func = { func : 'b. ('a, 'b) func }

type ('a, 'b) typed_func =
  | Ty of 'a ty
  | Poly of 'b poly_func

let ty_func (type a) (type b) (type c) : (a, b) func -> (b, a) typed_func =
  let open Ty in
  function
  | B_int_op _ -> Ty integer
  | U_int_op _ -> Ty integer
  | B_bint_op (_, i, _) -> Ty (int i)
  | U_bint_op (_, i, _) -> Ty (int i)
  | Of_int i -> Ty (int i)
  | To_int _ -> Ty integer
  | To_float r -> Ty (float r)
  | Of_float _ -> Ty real
  | B_bint_bop (_, i) -> Ty (int i)
  | U_bint_bop (_, i) -> Ty (int i)
  | Lsl_bint (i, _) -> Ty (int i)
  | B_num_pred _ -> Ty Bool
  | Poly _ -> Ty Bool
  | User _ as f -> Poly { func = f }

let func : type a b c. (a, b) ty_opt -> (c, b) func -> (c, a) func = fun t f ->
  match t with
  | Any -> f
  | Ty ty ->
    match ty_func f with
    | Poly { func } -> func
    | Ty ty' -> let Eq = eq_ty ty ty' in f

let ty_const (type a) (type b) : a constant -> a ty =
  let open Ty in
  function
  | Void -> Void
  | Int _ -> integer
  | Real _ -> real
  | Bool _ -> Bool

let const : type a b. (a, b) ty_opt -> b constant -> a constant = fun t c ->
  match t with
  | Any -> c
  | Ty ty ->
    let Eq = eq_ty ty (ty_const c) in c

type 'a poly_tconstr = { tconstr : 'b. ('a, 'b) tconstr }

type ('a, 'b) typed_tconstr =
  | Ty of 'a ty
  | Poly of 'b poly_tconstr

let ty_tconstr (type a) (type b) : (a, b) tconstr -> (b, a) typed_tconstr =
  function
  | Numeric n -> Ty (Numeric n)
  | Bool -> Ty Bool
  | Void -> Ty Void
  | Var _ as v -> Poly { tconstr = v }
  | User _ as u -> Poly { tconstr = u }

let tconstr : type a b c. (a, b) ty_opt -> (c, b) tconstr -> (c, a) tconstr = fun t tc ->
  match t with
  | Any -> tc
  | Ty ty ->
    match ty_tconstr tc with
    | Poly { tconstr } -> tconstr
    | Ty ty' -> let Eq = eq_ty ty ty' in tc

type poly_logic_type = { logic_type : 'a. 'a logic_type }

type 'a typed_logic_type =
  | Ty of 'a ty
  | Poly of poly_logic_type

let ty_logic_type (Type (tc, args) : _ logic_type) =
  match ty_tconstr tc with
  | Ty ty -> Ty ty
  | Poly { tconstr } -> Poly { logic_type = Type (tconstr, args) }

let logic_type ty (Type (tc, args) : _ logic_type) = (Type (tconstr ty tc, args) : _ logic_type)

type 'a typed_term =
  | Ty of 'a ty
  | Ty' of 'a ty
  | Poly of poly_term
  | Poly' of poly_term

let rec ty_term : type a. a term -> a typed_term =
  function
  | Const c -> Ty (ty_const c)
  | Var _ as v -> Poly { term = v }
  | App (f, args) ->
    begin match ty_func f with
    | Ty ty -> Ty ty
    | Poly { func } -> Poly { term = App (func, args) }
    end
  | Deref _
  | Deref_at _ as d -> Poly { term = d }
  | Typed (_, t') -> Ty t'
  | Poly _ as term -> Poly { term }
  | Labeled (lab, t) ->
    begin match ty_term t with
    | Ty ty | Ty' ty -> Ty' ty
    | Poly { term } | Poly' { term } -> Poly' { term = Labeled (lab, term) }
    end
  | If (i, t, e) ->
    begin match ty_term t with
    | Ty ty | Ty' ty -> Ty' ty
    | Poly { term = t } | Poly' { term = t } ->
      match ty_term e with
      | Ty _ | Ty' _ -> failwith "Cannot type term: branches have different type order"
      | Poly { term = e } | Poly' { term = e } ->
        Poly' { term = If (i, t, e) }
    end
  | Let (v, e, e') ->
    match ty_term e' with
    | Ty ty | Ty' ty -> Ty' ty
    | Poly { term } | Poly' { term } -> Poly' { term = Let (v, e, term) }

let rec term : type a b. (a, b) ty_opt -> b term -> a term = fun ty t ->
  match ty with
  | Any -> t
  | Ty ty ->
    match ty_term t with
    | Poly { term } -> term
    | Poly' { term } -> Poly { term }
    | Ty ty' -> let Eq = eq_ty ty ty' in t
    | Ty' ty' -> let Eq = eq_ty ty ty' in Typed (t, ty')

type 'a typed_why_type =
  | Ty of 'a ty
  | Ty' of 'a ty
  | Poly of poly_why_type
  | Poly' of poly_why_type

let rec ty_why_type : type a. a why_type -> a typed_why_type =
  function
  | Prod_type (_, t1, t2) ->
    begin match ty_why_type t1, ty_why_type t2 with
    | (Ty ty1 | Ty' ty1), (Ty ty2 | Ty' ty2) -> Ty' (Arrow (ty1, ty2))
    | (Ty ty1 | Ty' ty1), (Poly _ | Poly' _) -> Ty' (Arrow (ty1, Ex))
    | (Poly _ | Poly' _), (Ty ty1 | Ty' ty1) -> Ty' (Arrow (Ex, ty1))
    | (Poly _ | Poly' _), (Poly _ | Poly' _) -> Ty' (Arrow (Ex, Ex))
    end
  | Base_type lt ->
    begin match ty_logic_type lt with
    | Ty ty -> Ty ty
    | Poly { logic_type } -> Poly { why_type = Base_type logic_type }
    end
  | Ref_type r ->
    begin match ty_why_type r with
    | Ty ty | Ty' ty -> Ty' (Ref ty)
    | Poly _ | Poly' _ -> Ty' (Ref Ex)
    end
  | Annot_type (_ , wt, _, _, _, _) ->
    begin match ty_why_type wt with
    | Ty ty | Ty' ty -> Ty' ty
    | Poly poly | Poly' poly -> Poly' poly
    end
  | Typed (_, ty) -> Ty ty
  | Poly _ as why_type -> Poly { why_type }

let why_type : type a b. (a, b) ty_opt -> b why_type -> a why_type = fun t wt ->
  match t with
  | Any -> wt
  | Ty ty ->
    match ty_why_type wt with
    | Poly { why_type } -> why_type
    | Poly' { why_type } -> Poly { why_type }
    | Ty ty' -> let Eq = eq_ty ty ty' in wt
    | Ty' ty' -> let Eq = eq_ty ty ty' in Typed (wt, ty')

type 'a typed_expr =
  | Ty of 'a ty
  | Ty' of 'a ty
  | Poly of poly_expr
  | Poly' of poly_expr



(*
module R_expr = Return (struct type 'a t = 'a expr end)
let rec expr : type a b. (a, b) ty_opt -> b expr -> a expr = fun t e ->
  let open R_expr in
  let return = return t e in
  let return' expr_node = { e with expr_node } in
  match e.expr_node with
  | Cte c -> return' (Cte (const t c))
  | Var _ as v -> return' v
  | And _
  | Or _
  | Not _ -> return boolean
  | Void -> return void
  | Deref _ as d -> d
  | If (i, t', e) -> If (i, expr t t', expr t e)
  | While _
  | Block _
  | Assign _ -> return void
  | Let (v, e, e') -> Let (v, e, expr t e')
  | Let_ref (v, e, e') -> Let_ref (v, e, expr t e')
  | _ -> assert false

  (*| App : ('a, 'b) func * 'a expr_hlist * 'b why_type option -> 'b expr_node
  | Raise : string * 'a expr option -> 'b expr_node
  | Try : 'a expr * string * string option * 'a expr -> 'a expr_node
  | Fun : (string * any_why_type) list * 'b why_type * pred * 'b expr * pred * bool * ((string * pred) list) ->
    'b expr_node
    (** params * result_type * pre * body * post * diverges * signals *)
  | Triple : opaque * pred * 'a expr * pred * ((string * pred) list) -> 'a expr_node
  | Assert : assert_kind * pred -> void expr_node
  | Black_box : 'a why_type -> 'a expr_node
  | Absurd : void expr_node
    | Labeled : why_label * 'a expr -> 'a expr_node*)
*)
