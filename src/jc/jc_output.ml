open Output_ast

let (@) : _ term -> _ term_hlist -> _ term_hlist = fun x xs -> Cons (x, xs)

let (@.) : _ term -> _ term -> _ term_hlist = fun x y -> Cons (x, Cons (y, Nil))

let (@$) : _ func -> _ term_hlist -> _ term = fun x y -> App (x, y)

let (@$.) : _ func -> _ term -> _ term = fun x y -> App (x, Cons (y, Nil))


let expr ?labels:(expr_labels=[]) node = { expr_labels; expr_node = node }

let (@:) labels = expr ~labels

let (@@) : _ expr -> _ expr_hlist -> _ expr_hlist = fun x xs -> Cons (x, xs)

let (@@.) : _ expr -> _ expr -> _ expr_hlist = fun x y -> Cons (x, Cons (y, Nil))

let (@@$) : _ func -> _ expr_hlist -> _ expr_node = fun x y -> App (x, y, None)

let (@@$.) : _ func -> _ expr -> _ expr_node = fun x y -> App (x, Cons (y, Nil), None)

let (@@:) : _ expr_node -> _ why_type -> _ expr_node =
  fun e t ->
  match e with
  | App (x, y, None) -> App (x, y, Some t)
  | e -> e

let int8 : _ integer = Int (Signed, X8)

let uint8 : _ integer = Int (Unsigned, X8)

let int16 : _ integer = Int (Signed, X16)

let uint16 : _ integer = Int (Unsigned, X16)

let int32 : _ integer = Int (Signed, X32)

let uint32 : _ integer = Int (Unsigned, X32)

let int64 : _ integer = Int (Signed, X64)

let uint64 : _ integer = Int (Unsigned, X64)

let int n = Const (Int (string_of_int n))

let conv : type a b. (a, b) integer number -> (a, b) integer number term =
  fun ty ->
  let t = Of_int int8 @$. int 24 in
  match ty with
  | Integral (Int (Signed, X8))  -> t
  | _ -> failwith "incorrect type"

let x = conv (Integral int8)

let y = conv (Integral uint16)
