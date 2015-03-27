
open Stdlib
open Common
open Output_ast

module P = Pervasives
module S = Stdlib

module Ty =
struct
  type 'a t = 'a ty
  let integer : _ ty = Numeric (Integral Integer)
  let int i : _ ty = Numeric (Integral i)
  let float r : _ ty = Numeric (Real r)
  let real : _ ty = Numeric (Real Real)
end

let rec string_of_ty : type a. a ty -> string =
  function
  | (Numeric (Integral Integer) : a ty) -> "integer"
  | Numeric (Integral (Int (r, b))) -> string_of_some_enum (Env.Int (r, b))
  | Numeric (Integral (Enum e)) -> string_of_some_enum (Env.Enum e)
  | Numeric (Real Real) -> "real"
  | Numeric (Real (Float Single)) -> "single"
  | Numeric (Real (Float Double)) -> "double"
  | Bool -> "bool"
  | Void -> "void"
  | Ref r -> "ref " ^ string_of_ty r
  | Arrow (t1, t2) -> string_of_ty t1 ^ " -> " ^ string_of_ty t2
  | Ex -> "\"existential, i.e. some distinct type\""

type (_, _) eq = Eq : ('a, 'a) eq

let rec eq : type a b. a ty -> b ty -> (a, b) eq = fun a b ->
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
  | Numeric (Integral (Enum (module E1))),    Numeric (Integral (Enum (module E2))) ->
    begin match E1.E with
    | E2.E -> Eq
    | _ -> failwith ("Enum mismatch in Why3ML output: expected: `" ^ E1.name ^ "', got: `" ^ E2.name ^ "'")
    end
  | Numeric (Real Real),                      Numeric (Real Real) -> Eq
  | Numeric (Real (Float Single)),            Numeric (Real (Float Single)) -> Eq
  | Numeric (Real (Float Double)),            Numeric (Real (Float Double)) -> Eq
  | Bool,                                     Bool -> Eq
  | Void,                                     Void -> Eq
  | Ref ty,                                   Ref ty' -> let Eq = eq ty ty' in Eq
  | Arrow (t1, t2),                           Arrow (t1', t2') ->
    let Eq = eq t1 t1' in
    let Eq = eq t2 t2' in
    Eq
  | _ ->
    failwith ("Type mismatch in Why3ML output: expected: `" ^ string_of_ty a ^ "', got: `" ^ string_of_ty b ^ "'")

module C =
struct
  type 'a t = 'a constant

  let ty (type a) (type b) : a constant -> a ty =
    let open Ty in
    function
    | Void -> Void
    | Int _ -> integer
    | Real _ -> real
    | Bool _ -> Bool

  let check : type a b. (a, b) ty_opt -> b constant -> a constant = fun t c ->
    match t with
    | Any -> c
    | Ty ty' ->
      let Eq = eq ty' (ty c) in c
end

let f s ~from:(name, import) = (User (name, import, s) : _ func)

module F =
struct
  type ('a, 'b) t = ('a, 'b) func

  type 'a poly = { func : 'b. ('a, 'b) func }

  let jc = f ~from:Name.Theory.jessie

  let jc_val = f ~from:Name.Module.jessie

  type ('a, 'b) typed =
    | Ty of 'a ty
    | Poly of 'b poly

  let ty : type a b c. (a, b) func -> (b, a) typed =
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

  let check : type a b c. (a, b) ty_opt -> (c, b) func -> (c, a) func = fun t f ->
    match t with
    | Any -> f
    | Ty ty' ->
      match ty f with
      | Poly { func } -> func
      | Ty ty'' -> let Eq = eq ty' ty'' in f
end

module T =
struct
  type 'a t = 'a term

  type 'a hlist = 'a term_hlist

  let (@) : _ term -> _ term_hlist -> _ term_hlist = fun x xs -> Cons (x, xs)

  let (@.) : _ term -> _ term -> _ term_hlist = fun x y -> Cons (x, Cons (y, Nil))

  let (@$) : _ func -> _ term_hlist -> _ term = fun x y -> App (x, y)

  let (@$.) : _ func -> _ term -> _ term = fun x y -> App (x, Cons (y, Nil))

  let int n : _ term = Const (Int (string_of_int n))

  let num n : _ term = Const (Int (Num.string_of_num n))

  let void : _ term = Const Void

  let real s : _ term = Const (Real s)

  let bool b : _ term = Const (Bool b)

  let var s : _ term = Var s

  let positioned l_pos ?behavior:(l_behavior = "default") ?kind:l_kind t =
    (Labeled ({ l_kind; l_behavior; l_pos }, t) : _ term)

  let located l = positioned (Position.of_loc l)

  let positioned' l = positioned (Position.of_pos l)

  let bin op t1 t2 = B_int_op op @$ t1 @. t2

  let at v ~lab = Deref_at (v, lab)

  let if_ cond ~then_ ~else_ = If (cond, then_, else_)

  let let_ v ~equal ~in_ = Let (v, equal, in_ (var v))

  let (+) (t1 : _ term) (t2 : _ term) =
    match t1, t2 with
    | Const Int "0", _ -> t2
    | _, Const Int "0" -> t1
    | _ -> bin `Add t1 t2

  let (-) (t1 : _ term) (t2 : _ term) =
    match t1, t2 with
    | Const Int "0", _ -> t2
    | _, Const Int "0" -> t1
    | _ -> bin `Sub t1 t2

  let ( * ) (t1 : _ term) (t2 : _ term) =
    match t1, t2 with
    | Const Int "0", _
    | _, Const Int "0" -> int 0
    | Const Int "1", _ -> t2
    | _, Const Int "1" -> t1
    | _ -> bin `Mul t1 t2

  let (/) (t1 : _ term) (t2 : _ term) =
    match t1, t2 with
    | _, Const Int "0" -> failwith "/: division by zero in integer term"
    | Const Int "0", _ -> int 0
    | _, Const Int "1" -> t1
    | _ -> bin `Div t1 t2

  let (%) (t1 : _ term) (t2 : _ term) =
    match t1, t2 with
    | _, Const Int "0" -> failwith "/: division by zero in integer term"
    | Const Int "0", _
    | _, Const Int "1" -> int 0
    | _ -> bin `Mod t1 t2

  let (-~) =
    function
    | (Const Int "0" : _ term) -> int 0
    | t -> U_int_op `Neg @$. t

  let (!) v = (Deref v : _ term)

  let select mem p = F.jc "select" @$ mem @. p

  let ( **>) fi = select (var (Name.field_memory_name fi))

  type 'a typed =
    | Ty of 'a ty
    | Ty' of 'a ty
    | Poly of poly_term
    | Poly' of poly_term

  let rec ty : type a. a term -> a typed =
    function
    | Const c -> Ty (C.ty c)
    | Var _ as v -> Poly { term = v }
    | App (f, args) ->
      begin match F.ty f with
      | F.Ty ty -> Ty ty
      | F.Poly { F.func } -> Poly { term = App (func, args) }
      end
    | Deref _
    | Deref_at _ as d -> Poly { term = d }
    | Typed (_, t') -> Ty t'
    | Poly _ as term -> Poly { term }
    | Labeled (lab, t) ->
      begin match ty t with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { term } | Poly' { term } -> Poly' { term = Labeled (lab, term) }
      end
    | If (i, t, e) ->
      begin match ty t with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { term = t } | Poly' { term = t } ->
        match ty e with
        | Ty ty | Ty' ty -> Ty' ty
        | Poly { term = e } | Poly' { term = e } ->
          Poly' { term = If (i, t, e) }
      end
    | Let (v, e, e') ->
      match ty e' with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { term } | Poly' { term } -> Poly' { term = Let (v, e, term) }

  let rec term : type a b. (a, b) ty_opt -> b term -> a term = fun typ t ->
    match typ with
    | Any -> t
    | Ty ty' ->
      match ty t with
      | Poly { term } -> term
      | Poly' { term } -> Poly { term }
      | Ty ty'' -> let Eq = eq ty' ty'' in t
      | Ty' ty'' -> let Eq = eq ty' ty'' in Typed (t, ty')
end

module Tc =
struct
  type ('a, 'b) t = ('a, 'b) tconstr

  type 'a poly = { tconstr : 'b. ('a, 'b) tconstr }

  type ('a, 'b) typed =
    | Ty of 'a ty
    | Poly of 'b poly

  let ty (type a) (type b) : (a, b) tconstr -> (b, a) typed =
    function
    | Numeric n -> Ty (Numeric n)
    | Bool -> Ty Bool
    | Void -> Ty Void
    | Var _ as v -> Poly { tconstr = v }
    | User _ as u -> Poly { tconstr = u }

  let check : type a b c. (a, b) ty_opt -> (c, b) tconstr -> (c, a) tconstr = fun t tc ->
    match t with
    | Any -> tc
    | Ty ty' ->
      match ty tc with
      | Poly { tconstr } -> tconstr
      | Ty ty'' -> let Eq = eq ty' ty'' in tc
end

let lt s ~from:(name, import) = User (name, import, s)

module Lt =
struct
  type 'a t = 'a logic_type

  let (@) : _ logic_type -> _ ltype_hlist -> _ ltype_hlist = fun x xs -> Cons (x, xs)

  let (@.) : _ logic_type -> _ logic_type -> _ ltype_hlist = fun x y -> Cons (x, Cons (y, Nil))

  let (@$) : _ tconstr -> _ ltype_hlist -> _ logic_type = fun x y -> Type (x, y)

  let (@$.) : _ tconstr -> _ logic_type -> _ logic_type = fun x y -> Type (x, Cons (y, Nil))

  let var s : _ logic_type = Var s @$ Nil

  let bool = Bool @$ Nil

  let void = Void @$ Nil

  let integer = Numeric (Integral Integer) @$ Nil

  let int i = Numeric (Integral i) @$ Nil

  let enum s = Numeric (Integral (Enum s)) @$ Nil

  let real = Numeric (Real Real) @$ Nil

  let single = Numeric (Real (Float Single)) @$ Nil

  let double = Numeric (Real (Float Double)) @$ Nil

  let var v = Var v @$ Nil

  type poly_logic_type = { logic_type : 'a. 'a logic_type }

  type 'a typed =
    | Ty of 'a ty
    | Poly of poly_logic_type

  let ty (Type (tc, args) : _ logic_type) =
    match Tc.ty tc with
    | Tc.Ty ty -> Ty ty
    | Tc.Poly { Tc.tconstr } -> Poly { logic_type = Type (tconstr, args) }

  let logic_type ty (Type (tc, args) : _ logic_type) = (Type (Tc.check ty tc, args) : _ logic_type)
end

module Wt =
struct
  type 'a t = 'a why_type

  let base t = Base_type Lt.(t @$ Nil)

  let integer = P.(base @@ Numeric (Integral Integer))

  let bool = base Bool

  let void = base Void

  type 'a typed =
    | Ty of 'a ty
    | Ty' of 'a ty
    | Poly of poly_why_type
    | Poly' of poly_why_type

  let rec ty : type a. a why_type -> a typed =
    function
    | Prod_type (_, t1, t2) ->
      begin match ty t1, ty t2 with
      | (Ty ty1 | Ty' ty1), (Ty ty2 | Ty' ty2) -> Ty' (Arrow (ty1, ty2))
      | (Ty ty1 | Ty' ty1), (Poly _ | Poly' _) -> Ty' (Arrow (ty1, Ex))
      | (Poly _ | Poly' _), (Ty ty1 | Ty' ty1) -> Ty' (Arrow (Ex, ty1))
      | (Poly _ | Poly' _), (Poly _ | Poly' _) -> Ty' (Arrow (Ex, Ex))
      end
    | Base_type lt ->
      begin match Lt.ty lt with
      | Lt.Ty ty -> Ty ty
      | Lt.Poly { Lt.logic_type } -> Poly { why_type = Base_type logic_type }
      end
    | Ref_type r ->
      begin match ty r with
      | Ty ty | Ty' ty -> Ty' (Ref ty)
      | Poly _ | Poly' _ -> Ty' (Ref Ex)
      end
    | Annot_type (_ , wt, _, _, _, _) ->
      begin match ty wt with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly poly | Poly' poly -> Poly' poly
      end
    | Typed (_, ty) -> Ty ty
    | Poly _ as why_type -> Poly { why_type }

  let check : type a b. (a, b) ty_opt -> b why_type -> a why_type = fun t wt ->
    match t with
    | Any -> wt
    | Ty ty' ->
      match ty wt with
      | Poly { why_type } -> why_type
      | Poly' { why_type } -> Poly { why_type }
      | Ty ty'' -> let Eq = eq ty' ty'' in wt
      | Ty' ty'' -> let Eq = eq ty' ty'' in Typed (wt, ty')
end

module E =
struct
  type 'a t = 'a expr

  type 'a hlist = 'a expr_hlist

  let mk ?labels:(expr_labels=[]) node = { expr_labels; expr_node = node }

  let (@:) labels ({ expr_labels } as e) = { e with expr_labels = P.(labels @ expr_labels) }

  let (@) : _ expr -> _ expr_hlist -> _ expr_hlist = fun x xs -> Cons (x, xs)

  let (@.) : _ expr -> _ expr -> _ expr_hlist = fun x y -> Cons (x, Cons (y, Nil))

  let (@$) : _ func -> _ expr_hlist -> _ expr = fun x y -> mk (App (x, y, None))

  let (@$.) : _ func -> _ expr -> _ expr = fun x y -> mk (App (x, Cons (y, Nil), None))

  let (>:) : _ expr -> _ why_type -> _ expr =
    fun e t ->
    match e.expr_node with
    | App (x, y, None) -> { e with expr_node = App (x, y, Some t) }
    | _ -> e

  let positioned l_pos ?behavior:(l_behavior = "default") ?kind:l_kind e =
    { e with expr_node = Labeled ({ l_kind; l_behavior; l_pos }, e) }

  let located l = positioned (Position.of_loc l)

  let positioned' l = positioned (Position.of_pos l)

  let int n : _ t = mk (Const (Int (string_of_int n)))

  let num n : _ t = mk (Const (Int (Num.string_of_num n)))

  let var v = mk (Var v)

  let (!) v = mk (Deref v)

  let void = mk Void

  let let_ v ~equal ~in_ = mk (Let (v, equal, in_ (var v)))

  let let_ref v ~equal ~in_ = mk (Let_ref (v, equal, in_ (var v)))

  let (||) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | Const (Bool true), _ -> e1
    | _, Const (Bool true) -> e2
    | Const (Bool false), _ -> e2
    | _, Const (Bool false) -> e1
    | _, _ -> mk (Or (e1, e2))

  let (&&) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | Const (Bool true), _ -> e2
    | _, Const (Bool true)  -> e1
    | Const (Bool false), _ -> e1
    | _, Const (Bool false) -> e2
    | _, _ -> mk (And (e1, e2))

  let while_ cond ~inv ~var e =
    let body =
      match e.expr_node with
      | Block l -> l
      | _ -> [e]
    in
    mk (While (cond, inv, var, body))

  let block ?(labs=[]) =
    function
    | [] -> labs @: void
    | [e] -> labs @: e
    | l -> labs @: mk (Block l)

  let bin op t1 t2 = B_int_op op @$ t1 @. t2

  let (+) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | Const Int "0", _ -> e2
    | _, Const Int "0" -> e1
    | _ -> bin `Add e1 e2

  let (-) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | Const Int "0", _ -> e2
    | _, Const Int "0" -> e1
    | _ -> bin `Sub e1 e2

  let ( * ) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | Const Int "0", _
    | _, Const Int "0" -> int 0
    | Const Int "1", _ -> e2
    | _, Const Int "1" -> e1
    | _ -> bin `Mul e1 e2

  let (/) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | _, Const Int "0" -> failwith "/: division by zero in integer term"
    | Const Int "0", _ -> int 0
    | _, Const Int "1" -> e1
    | _ -> bin `Div e1 e2

  let (%) e1 e2 =
    match e1.expr_node, e2.expr_node with
    | _, Const Int "0" -> failwith "/: division by zero in integer term"
    | Const Int "0", _
    | _, Const Int "1" -> int 0
    | _ -> bin `Mod e1 e2

  let (-~) e =
    match e.expr_node with
    | Const Int "0" -> int 0
    | _ -> U_int_op `Neg @$. e

  let (!) v = (Deref v : _ term)

  let select mem p = F.jc "select" @$ mem @. p

  let ( **>) fi = select (var (Name.field_memory_name fi))

  type 'a typed =
    | Ty of 'a ty
    | Ty' of 'a ty
    | Poly of poly_expr_node
    | Poly' of poly_expr_node

  let rec ty : type a. a expr -> a typed = fun e ->
    match e.expr_node with
    | Const c -> Ty (C.ty c)
    | Var _ as expr_node -> Poly { expr_node }
    | And _ -> Ty Bool
    | Or _ -> Ty Bool
    | Not _ -> Ty Bool
    | Void  -> Ty Void
    | Deref _ as expr_node -> Poly { expr_node }
    | Typed (_, ty) -> Ty ty
    | Poly _ as expr_node -> Poly { expr_node }
    | If (i, t, e) ->
      begin match ty t with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { expr_node = t_expr_node } | Poly' { expr_node = t_expr_node } ->
        match ty e with
        | Ty ty | Ty' ty -> Ty' ty
        | Poly { expr_node } | Poly' { expr_node } ->
          Poly' { expr_node = If (i, { t with expr_node = t_expr_node }, { e with expr_node }) }
      end
    | While _ -> Ty Void
    | Block _ -> Ty Void
    | Assign _ -> Ty Void
    | Let (v, e, e') ->
      begin match ty e' with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { expr_node } | Poly' { expr_node } -> Poly' { expr_node = Let (v, e, { e' with expr_node }) }
      end
    | Let_ref (v, e, e') ->
      begin match ty e' with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { expr_node } | Poly' { expr_node } -> Poly' { expr_node = Let_ref (v, e, { e' with expr_node }) }
      end
    | App (f, args, rt) ->
      begin match F.ty f with
      | F.Ty ty -> Ty ty
      | F.Poly { F.func } ->
        match Option.map Wt.ty rt with
        | None -> Poly { expr_node = App (func, args, None) }
        | Some (Wt.Ty ty) -> Ty ty
        | Some (Wt.Ty' ty) -> Ty' ty
        | Some (Wt.Poly { why_type }) -> Poly { expr_node = App (func, args, Some why_type) }
        | Some (Wt.Poly' { why_type }) -> Poly' { expr_node = App (func, args, Some why_type) }
      end
    | Raise (ex, eo) -> Poly { expr_node = Raise (ex, eo) }
    | Try (e, ex, v, e') ->
      begin match ty e with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { expr_node = e_expr_node } | Poly' { expr_node = e_expr_node } ->
        match ty e' with
        | Ty ty | Ty' ty -> Ty' ty
        | Poly { expr_node } | Poly' { expr_node } ->
          Poly' { expr_node = Try ({ e with expr_node = e_expr_node }, ex, v, { e' with expr_node }) }
      end
    | Fun (args, rt, pre, e, post, div, raises) ->
      begin match Wt.ty rt with
      | Wt.Ty ty -> Ty ty
      | Wt.Ty' ty -> Ty' ty
      | Wt.Poly { why_type } | Wt.Poly' { why_type } ->
        match ty e with
        | Ty ty | Ty' ty -> Ty' ty
        | Poly { expr_node } | Poly' { expr_node } ->
          Poly' { expr_node = Fun (args, why_type, pre, { e with expr_node }, post, div, raises) }
      end
    | Triple (opaq, pre, e, post, raises) ->
      begin match ty e with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { expr_node } | Poly' { expr_node } ->
        Poly' { expr_node = Triple (opaq, pre, { e with expr_node }, post, raises) }
      end
    | Assert _ -> Ty Void
    | Black_box rt ->
      begin match Wt.ty rt with
      | Wt.Ty ty -> Ty ty
      | Wt.Ty' ty -> Ty' ty
      | Wt.Poly { why_type } ->
        Poly { expr_node = Black_box why_type }
      | Wt.Poly' { why_type } ->
        Poly' { expr_node = Black_box why_type }
      end
    | Absurd -> Ty Void
    | Labeled (lab, e) ->
      begin match ty e with
      | Ty ty | Ty' ty -> Ty' ty
      | Poly { expr_node } | Poly' { expr_node } -> Poly' { expr_node = Labeled (lab, { e with expr_node }) }
      end

  let rec check : type a b. (a, b) ty_opt -> b expr -> a expr = fun t e ->
    match t with
    | Any -> e
    | Ty ty' ->
      match ty e with
      | Poly { expr_node } -> { e with expr_node }
      | Poly' pen -> { e with expr_node = Poly pen }
      | Ty ty'' -> let Eq = eq ty' ty'' in e
      | Ty' ty'' -> let Eq = eq ty' ty'' in { e with expr_node = Typed (e, ty') }
end

module type Bounded =
sig
  type bound
  val ty : bound bounded integer
  val name : string
end

module type Form =
sig
  type 'a t
  type 'a hlist
  val (@.) : 'a t -> 'b t -> ('a * ('b * unit)) hlist
  val (@$) : ('a, 'b) F.t -> 'a hlist -> 'b t
  val (@$.) : ('a * unit, 'b) F.t -> 'a t -> 'b t
end

module Make_ops (I : Bounded) (F : Form) =
struct
  open F
  let bin op flag t1 t2 = T.(B_bint_op (op, I.ty, flag) @$ t1 @. t2)
  let un op flag t = T.(U_bint_op (op, I.ty, flag) @$. t)
  let (+) = bin `Add false
  let (+%) = bin `Add true
  let (-) = bin `Sub false
  let (-%) = bin `Sub true
  let ( * ) = bin `Mul false
  let ( *%) = bin `Mul true
  let (/) = bin `Div false
  let (/%) = bin `Div true
  let (%) = bin `Mod false
  let (%%) = bin `Mod true
end

module type Op_gen =
sig
  module type O
  module M : functor (_ : Form) -> O
end

module Make_enum (E : Enum) =
struct
  type bound = E.t enum
  let ty = Integral (Enum (module E))
  let name = E.name
end

module Make_bounded (I : Bounded) (O : Op_gen) =
struct
  include I
  let theory = String.capitalize name
  let safe_module = "Safe_" ^ name
  let unsafe_module = "Unsafe_" ^ name
  type t = I.bound bounded integer
  let rel pred t1 t2 : pred = App (B_num_pred (pred, Integral I.ty), T.(t1 @. t2))
  module T =
  struct
    include Make_ops (I) (T)
    let of_int t = T.(Of_int I.ty @$. t)
    let to_int t = T.(To_int I.ty @$. t)
    module B = O.M (T)
  end
  module E =
  struct
    include Make_ops (I) (E)
    let of_int t = E.(Of_int I.ty @$. t)
    let to_int t = E.(To_int I.ty @$. t)
    module B = O.M (E)
  end
  let (>) = rel `Gt
  let (>=) = rel `Ge
  let (<) = rel `Lt
  let (<=) = rel `Le
  let (=) = rel `Eq
  let (<>) = rel `Ne
end

module Enum (I : sig type bound' end) =
struct
  type bound = I.bound'
  let ty = failwith "The dummy functor Enum should never be applied"
  let name = "enum"
end

module Empty =
struct
  module type O = sig end
  module M (_ : Form) = struct end
end

module type Enum =
sig
  type bound
  include module type of Make_bounded (Enum (struct type bound' = bound end)) (Empty) with type bound := bound
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
  include Make_bounded
      (struct
        include I
        type bound = (I.r repr, I.b bit) xintx
      end)
      (struct
        module M (T : Form) =
        struct
          type 'a t = 'a T.t
          open T
          let bin op t1 t2 = T.(B_bint_bop (op, I.ty) @$ t1 @. t2)
          let un op t = T.(U_bint_bop (op, I.ty) @$. t)
          let (<<) (*>>)*) t1 t2 = T.(Lsl_bint (I.ty, false) @$ t1 @. t2)
          let (<<%) t1 t2 = T.(Lsl_bint (I.ty, true) @$ t1 @. t2)
          let (&) = bin `And
          let (||) = bin `Or
          let xor = bin `Xor
          let (>>) = bin `Lsr
          let (>>>) = bin `Asr
          let (~~) = un `Compl
        end
        module F (D : sig type 'a t' end) =
        struct
          type 'a t = 'a D.t'
          type 'a hlist
          let (@.) : 'a t -> 'b t -> ('a * ('b * unit)) hlist = fun _ _ -> assert false
          let (@$) : ('a, 'b) F.t -> 'a hlist -> 'b t = fun _ _ -> assert false
          let (@$.) : ('a * unit, 'b) F.t -> 'a t -> 'b t = fun _ _ -> assert false
        end
        module type O =
        sig
          type 'a t
          include module type of M (F (struct type 'a t' =  'a t end)) with type 'a t := 'a t
        end
      end)
  let bit_theory = "Bit" ^ name
  let safe_bit_module = "Safe_bit_" ^ name
  let unsafe_bit_module = "Unsafe_bit_" ^ name
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

let rel op t1 t2 : pred = T.(App (B_num_pred (op, Integral Integer), t1 @. t2))

let (>) = rel `Gt
let (>=) = rel `Ge
let (<) = rel `Lt
let (<=) = rel `Le

let (=) t1 t2 : pred = T.(App (Poly `Eq, t1 @. t2))
let (<>) t1 t2 : pred = T.(App (Poly `Neq, t1 @. t2))

module P =
  struct
    let rec unlabel : pred -> pred =
      function
      | Labeled (_, p) -> unlabel p
      | p -> p

    let positioned l_pos ?behavior:(l_behavior = "default") ?kind:l_kind p =
      (Labeled ({ l_kind; l_behavior; l_pos }, p) : pred)

    let located = S.(positioned % Position.of_loc)

    let positioned'  = S.(positioned % Position.of_pos)
  end

let is_not_true p =
  match P.unlabel p with
  | True -> false
  | _ -> true

let not p =
  match P.unlabel p with
  | True -> False
  | False -> True
  | _ -> Not p

let (&&) p1 p2 =
  match P.unlabel p1, P.unlabel p2 with
  | True, _ -> True
  | _, True -> True
  | False, _ -> p2
  | _, False -> p1
  | _, _ -> Or (p1, p2)

let (||) p1 p2 =
  match P.unlabel p1, P.unlabel p2 with
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
  match P.unlabel p1, P.unlabel p2 with
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
  match P.unlabel p1, P.unlabel p2 with
  | True, _ -> p2
  | _, True -> p1
  | False, _ -> not p2
  | _, False -> not p1
  | _, _ -> Iff (p1, p2)

let rec (^@) e1 e2 =
  let open E in
  match e1.expr_labels, e1.expr_node, e2.expr_labels, e2.expr_node with
  | labs1, Void, _, _ -> labs1 @: e2
  | _, _, [], Void -> e1
  | labs1, Block [], _, _ -> (labs1 @: void) ^@ e2
  | _, _, labs2, Block [] -> e1 ^@ labs2 @: void
  | labs1, Block [e1], _, _ -> (labs1 @: e1) ^@ e2
  | _, _, labs2, Block [e2] -> e1 ^@ labs2 @: e2
  | labs, Block l1, _, _ ->
    block ~labs (append l1 [e2])
  | labs, _, labs2, Block (e2 :: e2s) ->
    block ~labs (append [e1] ((labs2 @: e2) :: e2s))
  | labs, _, _, _ ->
    block ~labs [{ e1 with expr_labels = [] }; e2]

and append l1 l2 =
  let open E in
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

type some_expr_hlist = Expr_hlist : _ expr_hlist -> some_expr_hlist

let args_e =
  List.fold_left (fun (Expr_hlist ehl) (Expr e) -> Expr_hlist E.(e @ ehl)) (Expr_hlist Nil)

let id { why_id } = why_id

let why_decl ~name:why_name ?expl:(why_expl="") ?pos:(why_pos = Position.dummy) why_decl =
  { why_id = { why_name; why_expl; why_pos }; why_decl }

let jc_lt = lt ~from:Name.Theory.jessie

open Name

let select_commited pc = T.(select (var (committed_name pc)))

let typeof tt p = T.(F.jc "typeof" @$ tt @. p)

let typeeq tt p st = typeof tt p = T.var (Name.tag st)

let (<:) t1 t2 : pred = App (F.jc "subtag", T.(t1 @. t2))

let instanceof tt p st : pred = App (F.jc "instanceof", T.(tt @ p @. var (Name.tag st)))

let disjoint ps1 ps2 : pred = App (F.jc "pset_disjoint", T.(ps1 @. ps2))

let alloc_table ?r ac =
  T.var (Option.map_default r ~default:(Name.Generic.alloc_table ac) ~f:(fun r -> Name.alloc_table (ac, r)))

let offset_min ac ?r p = T.(F.jc "offset_min" @$ alloc_table ?r ac @. p)

let offset_max ac ?r p = T.(F.jc "offset_max" @$ alloc_table ?r ac @. p)

let int_of_tag st = T.(F.jc "int_of_tag" @$. var (Name.tag st))

let some (type a) (type b) : (a, b) ty_opt -> _ =
  function
  | Ty _ as t -> t
  | Any ->
    failwith "Polymorphic type was expected, but monomorphic AST node was encountered"
