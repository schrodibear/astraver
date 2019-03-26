(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  AstraVer fork:                                                        *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

module Fn =
struct
  type ('a, 'b) t = 'a -> 'b

  external id : 'a -> 'a = "%identity"
  let compose f g x = f (g x)
  let const r _ = r
  let tap f x = f x; x
  let on cond f x =
    if cond then f x
    else x
  let on' cond f x =
    if cond then f () x
    else x
  let pipe_compose f g x = g (f x)
  let uncurry f (a, b) = f a b
  let curry f a b = f (a, b)
  let flip f a b = f b a
end

let (%) = Fn.compose

let (%>) = Fn.pipe_compose

let (%%) f g h x y = f (g x) (h y)

module Tuple =
struct
  module T2 =
  struct
    type ('a, 'b) t = 'a * 'b

    let dup2 a = a, a
    let fdup2 ~f ~g x = f x, g x
    let cons a b = (a, b)
    let cons' b a = (a, b)
    let map1 ~f (a, b) = f a, b
    let map2 ~f (a, b) = a, f b
    let map ~f (a, b) = f a, f b
    let map_2 ~f ~g (a, b) = f a, g b
    let fold_left ~f ~init (a, b) = f (f init a) b
    let fold = fold_left
    let fold_right ~f (a, b) ~init = f a (f b init)
    let fold_left' ~f ab init = fold_left f init ab
    let fold_right' ~f ab init = fold_right f ab init
    let swap (a, b) = b, a
  end
  module T3 =
  struct
    let fst (a, _, _) = a
    let snd (_, b, _) = b
    let trd (_, _, c) = c
    let fdup3 ~f ~g ~h x = f x, g x, h x
    let map1 ~f (a, b, c) = f a, b, c
    let map2 ~f (a, b, c) = a, f b, c
    let map3 ~f (a, b, c) = a, b, f c
  end
end

module Pair = Tuple.T2

let dup2 = Pair.dup2

let fdup2 f g = Pair.fdup2 ~f ~g

let map_fst f = Pair.map1 ~f

let map_snd f = Pair.map2 ~f

let swap = Pair.swap

module Triple = Tuple.T3

let fdup3 f g h = Triple.fdup3 ~f ~g ~h

module Monad_def =
struct
  module type S =
  sig
    type 'a m
    val return : 'a -> 'a m
    val bind : 'a m -> ('a -> 'b m) -> 'b m
  end
end

module Monad =
struct
  module type S =
    sig
      include Monad_def.S
      val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
      val (>>) : 'a m -> 'b m -> 'b m
    end

  module Make (M : Monad_def.S) : S =
  struct
    include M
    let (>>=) = M.bind
    let (>>) m1 m2 = M.bind m1 (fun _ -> m2)
  end

  module Make_subst (M : Monad_def.S) : S with type 'a m := 'a M.m =
  struct
    include M
    let (>>=) = M.bind
    let (>>) m1 m2 = M.bind m1 (fun _ -> m2)
  end
end

module Option =
struct
  let value ~default =
    function
    | Some x -> x
    | None -> default

  let value_exn ~exn =
    function
    | Some x -> x
    | None -> raise exn

  let value_fail ~in_ =
    function
    | Some x -> x
    | None -> failwith ("Tried to get some value from None in " ^ in_)

  let compare ~cmp a b =
    match a, b with
    | Some a, Some b -> cmp a b
    | None, Some _ -> -1
    | Some _, None -> 1
    | None, None -> 0

  let equal ~eq a b =
    match a, b with
    | Some a, Some b -> eq a b
    | None, Some _
    | Some _, None -> false
    | None, None -> true

  include
    (Monad.Make_subst
       (struct
         type 'a m = 'a option
         let bind m f =
           match m with
           | Some v -> f v
           | None -> None
         let return v = Some v
       end))

  let abort = None

  let some x = Some x
  let map ~f =
    function
    | None -> None
    | Some x -> Some (f x)

  let map_default ~default ~f =
    function
    | None -> default
    | Some x -> f x

  let fold_left ~f ~init =
    function
    | Some x -> f init x
    | None -> init

  let fold = fold_left

  let fold_right ~f o ~init =
    match o with
    | Some x -> f x init
    | None -> init

  let fold_left' ~f o init = fold_left ~f ~init o

  let fold_right' ~f o init = fold_right ~f o ~init

  let iter ~f =
    function
    | None -> ()
    | Some x -> f x

  let is_some =
    function
    | Some _ -> true
    | None -> false

  let is_none o = not (is_some o)
end

let (|?) xo default = Option.value ~default xo

module String =
struct
  include String

  let capitalize = capitalize_ascii
  let lowercase = lowercase_ascii
end

module List =
struct
  include List

  let cons e l = e :: l

  let cons' l e = e :: l

  let fold_left' ~f l init = fold_left f init l

  let fold_right' ~f l init = fold_right f l init

  let range i dir j =
    try
      let op =
        match dir with
        | `To when i <= j -> pred
        | `Downto when i >= j -> succ
        | _ -> raise Exit
      in
      let rec loop acc k =
        if i = k then
          k :: acc
        else
          loop (k :: acc) (op k)
      in
      loop [] j
    with
    | Exit -> []

  let as_singleton =
    function
    | [e] -> e
    | _ -> failwith "as_singleton: non-singleton list"

  let mem_assoc_eq f k l =
    fold_left
      (fun v_opt (k', v') ->
         match v_opt with
         | None ->
           if f k k' then Some v' else None
         | Some v -> Some v)
      None
      l

  let rec all_pairs ?(acc=[]) =
    function
    | e :: l ->
      let acc = fold_left (fun acc e' -> (e,e') :: acc) acc l in
      all_pairs ~acc l
    | [] -> acc

  let all_ordered_pairs l = flatten @@ map (fun x -> map (Pair.cons x) l) l

  let concat_map ~f l =
    let rec aux acc =
      function
      | [] -> List.rev acc
      | hd :: tl -> aux (rev_append (f hd) acc) tl
    in
    aux [] l

  let map_fold f acc l =
    let rev, acc =
      fold_left
        (fun (rev, acc) e -> let (e, acc) = (f acc e) in e :: rev, acc)
        ([], acc)
        l
    in
    List.rev rev,acc

  let rec fold_all_part f ?(part=[]) acc =
    function
    | [] -> f acc part
    | a :: l -> fold_all_part f (fold_all_part f ~part:(a :: part) acc l) ~part l

  let group_consecutive ~p =
    let rec loop acc last_group =
      function
      | x :: (y :: _ as xs) when p x y -> loop acc (y :: last_group) xs
      | _ :: (y :: _ as xs) -> loop ((rev last_group) :: acc) [y] xs
      | _ -> rev (last_group :: acc)
    in
    function
    | [] -> []
    | [x] -> [[x]]
    | x :: _ as xs -> loop [] [x] xs

  let rec last =
    function
    | [x] -> x
    | _ :: xs -> last xs
    | [] -> failwith "last"

  let rec but_last ?(acc=[]) =
    function
    | [] | [_] -> rev acc
    | x :: xs -> but_last ~acc:(x :: acc) xs
end

module Set =
struct

  module type OrderedType = Set.OrderedType

  module type S = sig
    include Set.S
    val of_list: elt list -> t
    val to_list: t -> elt list
  end

  module Make(Ord : OrderedType) : S with type elt = Ord.t = struct
    include Set.Make(Ord)

    let of_list ls =
      List.fold_left (fun s e -> add e s) empty ls

    let to_list s =
      fold (fun e acc -> e :: acc) s []

  end
end

module Map =
struct

  module type OrderedType = Map.OrderedType

  module type S = sig
    include Map.S
    val elements: 'a t -> (key * 'a) list
    val keys: 'a t -> key list
    val values: 'a t -> 'a list
    val to_list: 'a t -> (key * 'a) list
    val find_or_default: key -> 'a -> 'a t -> 'a
    val find_or_none: key -> 'a t -> 'a option
    val merge: ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    val add_merge: ('a -> 'a -> 'a) -> key -> 'a -> 'a t -> 'a t
    val diff_merge: ('a -> 'a -> 'a) -> ('a -> bool) -> 'a t -> 'a t -> 'a t
    val inter_merge: ('a -> 'a -> 'a) -> ('a -> bool) -> 'a t -> 'a t -> 'a t
    val inter_merge_option: ('a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
  end

  module Make(Ord : OrderedType) : S with type key = Ord.t = struct
    include Map.Make(Ord)

    let elements m =
      fold (fun k v acc -> (k, v) :: acc) m []

    let keys m =
      fold (fun k _v acc -> k :: acc) m []

    let values m =
      fold (fun _k v acc -> v :: acc) m []

    let to_list m =
      fold (fun k v acc -> (k, v) :: acc) m []

    let find_or_default k v m =
      try find k m with Not_found -> v

    let find_or_none k m =
      try Some (find k m) with Not_found -> None

    let merge f m1 m2 =
      fold
        (fun k v1 m ->
           try
             let v2 = find k m2 in
             add k (f v1 v2) m
           with
           | Not_found ->
             add k v1 m)
        m1
        m2

    let add_merge f k v m =
      let v =
        try f v (find k m)
        with Not_found -> v
      in
      add k v m

    let diff_merge f g m1 m2 =
      fold
        (fun k v1 m ->
           try
             let v2 = find k m2 in
             let v = f v1 v2 in
             if g v then m else add k v m
           with
           | Not_found ->
             add k v1 m)
        m1
        empty

    let inter_merge f g m1 m2 =
      fold
        (fun k v1 m ->
           try
             let v2 = find k m2 in
             let v = f v1 v2 in
             if g v then m else add k v m
           with
           | Not_found -> m)
        m1
        empty

    let inter_merge_option f m1 m2 =
      fold
        (fun k v1 m ->
           try
             let v2 = find k m2 in
             match f v1 v2 with
             | Some v -> add k v m
             | None -> m
           with Not_found -> m)
        m1
        empty

  end
end

module StdHashtbl = Hashtbl

module Hashtbl =
struct

  module type HashedType = Hashtbl.HashedType

  module type S = sig
    include Hashtbl.S
    val keys: 'a t -> key list
    val values: 'a t -> 'a list
    val choose: 'a t -> (key * 'a) option
    val remove_all : 'a t -> key -> unit
    val is_empty : 'a t -> bool
  end

  module type Std = sig
    type ('a, 'b) t
    val create : ?random:bool -> int -> ('a, 'b) t
    val clear : ('a, 'b) t -> unit
    val add : ('a, 'b) t -> 'a -> 'b -> unit
    val copy : ('a, 'b) t -> ('a, 'b) t
    val find : ('a, 'b) t -> 'a -> 'b
    val find_all : ('a, 'b) t -> 'a -> 'b list
    val mem : ('a, 'b) t -> 'a -> bool
    val remove : ('a, 'b) t -> 'a -> unit
    val replace : ('a, 'b) t -> 'a -> 'b -> unit
    val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
    val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
    val length : ('a, 'b) t -> int
    val hash : 'a -> int
    val hash_param : int -> int -> 'a -> int
  end

  include (Hashtbl : Std)

  module Make(H : HashedType) : S with type key = H.t = struct
    include Hashtbl.Make(H)

    let keys t =
      fold (fun k _v acc -> k :: acc) t []

    let values t =
      fold (fun _k v acc -> v :: acc) t []

    let choose t =
      let p = ref None in
      begin
        try
          iter (fun k v -> p := Some (k, v); failwith "Hashtbl.choose") t
        with
          Failure "Hashtbl.choose" -> ()
      end;
      !p

    let remove_all t p =
      List.iter (fun _ -> remove t p) (find_all t p)

    let is_empty t =
      try
        iter (fun _ _ -> raise Exit) t;
        true
      with
      | Exit -> false
  end

  let remove_all t p =
    List.iter (fun _ -> remove t p) (find_all t p)

  let is_empty t =
    try
      iter (fun _ _ -> raise Exit) t;
      true
    with
    | Exit -> false

end

(*
Local Variables:
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End:
*)
