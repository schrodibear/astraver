(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
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

let (%) f g x = f (g x)

let (%%) f g h x y = f (g x) (h y)

let (%>) f g x = g (f x)

let const r _ = r

let id x = x

let dup2 a = a, a

let fdup2 f g x = f x, g x

let map_fst f (a, b) = f a, b

let map_snd f (a, b) = a, f b

let map_pair f (a, b) = f a, f b

let map_pair2 f g (a, b) = f a, g b

let fold_left_pair f init (a, b) = f (f init a) b

let fold_right_pair f (a, b) init = f a (f b init)

let uncurry f (a, b) = f a b

let curry f a b = f (a, b)

let swap (a, b) = b, a

let fdup3 f g h x = f x, g x, h x

module type MONAD_DEF = sig
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module type MONAD = sig
  include MONAD_DEF
  val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  val (>>) : 'a m -> 'b m -> 'b m
end

module Monad (M : MONAD_DEF) = struct
  include M
  let (>>=) = M.bind
  let (>>) m1 m2 = M.bind m1 (fun _ -> m2)
end

module Option_monad = struct
  include Monad
    (struct
      type 'a m = 'a option
      let bind m f =
        match m with
        | Some v -> f v
        | None -> None
      let return v = Some v
    end)

  let abort = None

  let default v m =
    match m with
    | Some v -> v
    | None -> v
end

module List = struct
  include List

  let cons e l = e :: l

  let range i dir j =
    try
      let op =
        match dir with
        | `To ->
          if i <= j then pred
                    else raise Exit
        | `Downto ->
          if i >= j then succ
                    else raise Exit
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
    | _ -> failwith "as_singleton"

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

  let group_consecutive p =
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

end

module Set = struct

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

module Map = struct

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

module Hashtbl = struct

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
