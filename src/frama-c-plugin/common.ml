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
(*  Jessie2 fork:                                                         *)
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

(* Import from Cil *)
open Cil_types
open Cil
open Ast_info
open Extlib
open Visitor
open Cil_datatype

(* Utility functions *)
open Format

module Emitters =
struct
  type t = Emitter.t

  let jessie =
    Emitter.create
      "jessie"
      [Emitter.Funspec; Emitter.Code_annot]
      ~correctness:[Jessie_options.Behavior.parameter]
      ~tuning:[]

  let jessie_assume =
    Emitter.create
      "jessie_assume"
      [Emitter.Funspec; Emitter.Code_annot]
      ~correctness:[Jessie_options.Behavior.parameter]
      ~tuning:[]
end

exception Unsupported of string

module Console =
struct
  open Jessie_options

  let fatal fmt = fatal ~current:true fmt
  let abort ?source fmt = abort ?source fmt
  let error fmt = error ~current:true fmt
  let unsupported fmt =
    Jessie_options.with_failure
      (fun evt ->
         raise @@ Unsupported (may_map ~dft:"unknown feature" (fun evt -> evt.Log.evt_message) evt))
      ~current:true
      fmt
  let feedback fmt = feedback fmt
  let general_warning fmt = warning ~current:false fmt
  let warning fmt = warning ~current:true fmt
  let warn_once =
    let known_warns = Hashtbl.create 7 in
    fun s ->
      if not (Hashtbl.mem known_warns s) then begin
        Hashtbl.add known_warns s ();
        general_warning "%s" s
      end
  let debug fmt = debug fmt

  let debug_at_least = debug_atleast
  let verbose_at_least = verbose_atleast
end

module List =
struct
  include List

  type 'a t = 'a list

  let rev_filter_map l ~f =
    let rec loop l accum =
      match l with
      | [] -> accum
      | hd :: tl ->
        match f hd with
        | Some x -> loop tl (x :: accum)
        | None   -> loop tl accum
    in
    loop l []

  let filter_map l ~f = List.rev (rev_filter_map l ~f)

  let find_map t ~f =
    let rec loop =
      function
      | [] -> None
      | x :: l ->
        match f x with
        | None -> loop l
        | Some _ as r -> r
    in
    loop t

  let split3 list =
    let rec loop l1 l2 l3 =
      function
      | [] -> List.rev l1, List.rev l2, List.rev l3
      | (x, y, z) :: tl -> loop (x :: l1) (y :: l2) (z :: l3) tl
    in
    loop [] [] [] list

  let rec drop n lst =
    if n <= 0 then lst
    else
      match lst with
      | [] -> []
      | _ :: xs -> drop (n - 1) xs

  let take n lst =
    let rec take acc n =
      function
      | x :: xs when n > 0 -> take (x :: acc) (n - 1) xs
      | _ -> List.rev acc
    in
    take [] n lst

  let range i dir j =
    let op =
      match dir with
      | `To ->
        if i <= j then pred
        else invalid_arg (Printf.sprintf "Common.range %d `To %d" i j)
      | `Downto ->
        if i >= j then succ
        else invalid_arg (Printf.sprintf "Common.range %d `Downto %d" i j)
    in
    let rec loop acc k =
      if i = k then
        k :: acc
      else
        loop (k :: acc) (op k)
    in
    loop [] j

  let foldi f init t = snd @@ fold_left (fun (i, acc) v -> i + 1, f i acc v) (0, init) t

  let groupi ~break l =
    let groups =
      foldi
        (fun i acc x ->
           match acc with
           | []      -> [[x]]
           | g :: tl -> if break i (hd g) x
                        then [x] :: g :: tl
                        else (x :: g) :: tl)
           []
           l
    in
    match groups with
    | [] -> []
    | l  -> rev_map rev l

  let group ~break l = groupi l ~break:(fun _ x y -> break x y)
end

module String =
struct
  include String

  let explode s =
    let rec next acc i =
      if i >= 0 then next (s.[i] :: acc) (i-1) else acc
    in
    next [] (String.length s - 1)

  let implode ls =
    let s = Bytes.create (List.length ls) in
    ignore (List.fold_left (fun i c -> Bytes.set s i c; i + 1) 0 ls);
    Bytes.to_string s

  let filter_alphanumeric ~assoc ~default s =
    let is_alphanum c =
      String.contains "abcdefghijklmnopqrstuvwxyz" c
      || String.contains "ABCDEFGHIJKLMNOPQRSTUVWXYZ" c
      || String.contains "0123456789" c
      || c = '_'
    in
    let alphanum_or_default c =
      if is_alphanum c then c
      else try List.assoc c assoc with Not_found -> default
    in
    implode (List.map alphanum_or_default (explode s))
end

module Tuple =
struct
  module T2 =
  struct
    type ('a, 'b) t = 'a * 'b

    let fdup2 ~f ~g x = f x, g x
    let map1 ~f (a, b) = f a, b
    let map2 ~f (a, b) = a, f b
    let map ~f (a, b) = f a, f b
    let iter ~f (a, b) = f a; f b
    let swap (a, b) = b, a
  end
end

module Pair = Tuple.T2

module Fn =
struct
  type ('a, 'b) t = 'a -> 'b

  let id = Extlib.id
  let compose f g x = f (g x)
  let pipe_compose f g x = g (f x)
  let uncurry f (a, b) = f a b
  let flip = swap
end

let (%) = Fn.compose

let (%>) = Fn.pipe_compose

let fdup2 f g = Pair.fdup2 ~f ~g
let map_fst f = Pair.map1 ~f
let map_snd f = Pair.map2 ~f
let map_pair f = Pair.map ~f
let iter_pair f = Pair.iter ~f
let swap = Pair.swap

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

  let value_fatal ~in_ =
    function
    | Some x -> x
    | None -> Console.fatal "Tried to get some value from None in %s" in_

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
  let map ~f =
    function
    | None -> None
    | Some x -> Some (f x)

  let map_default ~default ~f =
    function
    | None -> default
    | Some x -> f x

  let fold ~init ~f =
    function
    | Some x -> f init x
    | None -> init

  let iter ~f =
    function
    | None -> ()
    | Some x -> f x

  let is_some =
    function
    | Some _ -> true
    | None -> false
end

let (|?) xo default = Option.value ~default xo

let (!!) = Lazy.force

module Filepath =
struct
  include Filepath
  let is_unknown loc = (fst loc).Filepath.pos_lnum = 0
end

module Loc =
struct
  type t = Lexing.position * Lexing.position
  let is_unknown loc = (fst loc).Lexing.pos_lnum = 0
  let to_position loc =
    Lexing.{
      Filepath.
      pos_lnum = loc.pos_lnum;
      pos_cnum = loc.pos_cnum;
      pos_bol = loc.pos_bol;
      pos_path = Filepath.Normalized.of_string loc.pos_fname
    }
  let of_position pos =
    Filepath.{
      Lexing.
      pos_lnum = pos.pos_lnum;
      pos_cnum = pos.pos_cnum;
      pos_bol = pos.pos_bol;
      pos_fname = (pos.pos_path :> string)
    }
  let to_location = map_pair to_position
  let of_location = map_pair of_position
end

module Framac =
struct
  module Ast = Ast
  module Type = Type
  module Vi = Varinfo
  module Config = Config
end

module Config =
struct
  include Jessie_options
  let flatten_multi_dim_arrays = false
end

(* Redefine statement constructor of CIL to create them with valid sid *)
let mkStmt = mkStmt ~valid_sid:true

module Name =
struct
  module Attr =
  struct
    let embedded = "embedded_from"
    let noembed = "noembed"
    let packed = "packed"
    let padding = "padding"
    let wrapper = "wrapper"
    let arraylen = "arraylen"
    let string_declspec = "valid_string"
  end

  module Predicate =
  struct
    let valid_string = "valid_string"
    let valid_wstring = "valid_wstring"
  end

  module Logic_function =
  struct
    let strlen = "strlen"
    let wcslen = "wcslen"
    let nondet_int = "jessie_nondet_int"
  end

  module Function =
  struct
    let assert_ = "assert"
    let free = "free"
    let kfree = "kfree"
    let kzfree = "kzfree"
    let malloc = "malloc"
    let kmalloc = "kmalloc"
    let kzalloc = "kzalloc"
    let calloc = "calloc"
    let realloc = "realloc"
    let memdup = "memdup"
    let kmemdup = "kmemdup"
    let alloca = "__builtin_alloca"
  end

  module File =
  struct
    let blockfuns_include = "jessie_spec_prolog.h"
  end

  let typ ty =
    ignore (flush_str_formatter ());
    fprintf str_formatter "%a" Printer.pp_typ ty;
    let name = flush_str_formatter () in
    String.filter_alphanumeric ~assoc:['*', 'x'] ~default:'_' name

  let logic_type ty =
    ignore (flush_str_formatter ());
    let old_mode = Kernel.Unicode.get() in
    Kernel.Unicode.set false;
    fprintf str_formatter "%a" Printer.pp_logic_type ty;
    let name = flush_str_formatter () in
    Kernel.Unicode.set old_mode;
    String.filter_alphanumeric ~assoc:['*', 'x'] ~default:'_' name

  module Logic_type =
  struct
    let set = "set"
    let padding = "padding"
  end

  module Behavior =
  struct
    let safety = "safety"
    let default = "default"
  end

  module Jc_specific =
  struct
    let hint = "hint"
  end

  let predefined_name =
    Function.[ (* coding functions *)
      assert_;
      malloc;
      kmalloc;
      kzalloc;
      calloc;
      realloc;
      memdup;
      kmemdup;
      alloca;
      free;
      kfree;
      kzfree;
      Logic_type.set;
      Logic_function.nondet_int
    ]

  let is_predefined s = List.mem s predefined_name

  let unique_generator is_exception =
    let unique_names = Hashtbl.create 127 in
    let rec aux ?(force=false) s =
      if not force && is_exception s then s
      else
        let s = if s = "" then "unnamed" else s in
        let s = if s.[0] <> Char.lowercase_ascii s.[0] then "_" ^ s else s in
        try
          let count = Hashtbl.find unique_names s in
          let s = s ^ "_" ^ (string_of_int !count) in
          if Hashtbl.mem unique_names s then
            aux s
          else begin
            Hashtbl.add unique_names s (ref 0);
            incr count;
            s
          end
        with
        | Not_found ->
          Hashtbl.add unique_names s (ref 0);
          s
    in
    let add s = Hashtbl.add unique_names s (ref 0) in
    aux, add

  let unique, add_unique =
    unique_generator is_predefined

  module Logic =
    struct
      let unique, add_unique =
        unique_generator (fun _ -> false)

      let unique = unique ~force:true
    end

  let unique_if_empty s =
    if s = "" then unique "unnamed" else s

  let jessie_reserved_names =
  [
    (* a *) "abstract"; "allocates"; "and"; "as"; "assert";
            "assigns"; "assumes"; "axiom"; "axiomatic";
    (* b *) "behavior"; "boolean"; "break";
    (* c *) "case"; "catch"; "check"; "continue";
    (* d *) "decreases"; "default"; "do"; "double";
    (* e *) "else"; "end"; "ensures"; "exception";
    (* f *) "false"; "finally"; "float"; "for"; "free";
    (* g *) "goto";
    (* h *) "hint";
    (* i *) "if"; "in"; "integer"; "invariant";
    (* l *) "lemma"; "let"; "logic"; "loop";
    (* m *) "match";
    (* n *) "new"; "null";
    (* o *) "of";
    (* p *) "pack"; "predicate";
    (* r *) "reads"; "real"; "rep"; "requires"; "return";
    (* s *) "switch";
    (* t *) "tag"; "then"; "throw"; "throws"; "true"; "try"; "type";
    (* u *) "unit"; "unpack";
    (* v *) "var"; "variant";
    (* w *) "while"; "with";
  ]

  let () =
    List.iter add_unique jessie_reserved_names;
    List.iter Logic.add_unique jessie_reserved_names
end

module Ast =
struct

  module Exp =
  struct
    type t = exp

    let const ?(loc=Location.unknown) n =
      Ast_info.constant_expr ~loc n

    let dummy_info e =
      match e.enode with
      | Info _ -> e
      | _ ->
        let einfo = { exp_type = Ctype voidPtrType; exp_name = [] } in
        (* In many cases, the correct type may not be available, as
         * the expression may result from a conversion from a term or a tset.
         * Calling [typeOf] on such an expression may raise an error.
         * Therefore, put here a dummy type until tsets correctly typed.
         *)
        new_exp ~loc:e.eloc @@ Info (e, einfo)

    let rec strip_casts_to ty =
      let norm = type_remove_qualifier_attributes_deep in
      function
      | { enode = CastE (ty', _, e) } when not (need_cast (norm ty') @@ norm ty) -> strip_casts_to ty e
      | e -> e
  end

  module Vi =
  struct
    type var
    type func
    type 'a t = varinfo
    type 'a t' = 'a t

    module Function =
    struct
      type t = func t'

      let of_varinfo vi =
        try
          Some (ignore (Globals.Functions.get vi : kernel_function); vi)
        with
        | Not_found -> None

      let of_varinfo_exn vi =
        try
          ignore (Globals.Functions.get vi : kernel_function); vi
        with
        | Not_found -> invalid_arg "Ast.Vi.Function.of_vi_exn: no function for varinfo"

      open Name.Function
      let is_assert v = isFunctionType v.vtype && v.vname = assert_
      let is_free v = isFunctionType v.vtype && v.vname = free
      let is_kfree v = isFunctionType v.vtype && v.vname = kfree
      let is_kzfree v = isFunctionType v.vtype && v.vname = kzfree
      let is_malloc v = isFunctionType v.vtype && v.vname = malloc
      let is_kmalloc v = isFunctionType v.vtype && v.vname = kmalloc
      let is_kzalloc v = isFunctionType v.vtype && v.vname = kzalloc
      let is_calloc v = isFunctionType v.vtype && v.vname = calloc
      let is_realloc v = isFunctionType v.vtype && v.vname = realloc
      let is_memdup v = isFunctionType v.vtype && v.vname = memdup
      let is_kmemdup v = isFunctionType v.vtype && v.vname = kmemdup
      let is_alloca v = isFunctionType v.vtype && v.vname = alloca

      let malloc ?(kernel=false) () =
        let fname, params =
          let size = "size", theMachine.typeOfSizeOf, [] in
          if not kernel then
            malloc, Some [size]
          else
            kmalloc, Some [size; "flags", intType, []]
        in
        let typ = TFun (voidPtrType, params, false, []) in
        try
          let vi = Kernel_function.get_vi (Globals.Functions.find_by_name fname) in
          if not @@ Typ.equal vi.vtype typ then begin
            setReturnTypeVI vi voidPtrType;
            setFormalsDecl vi typ;
            raise Not_found
          end;
          vi
        with
        | Not_found ->
          let f =
            findOrCreateFunc (Ast.get ()) fname typ
          in
          let prm =
            try
              List.hd (Cil.getFormalsDecl f)
            with Not_found | Invalid_argument _ ->
              Console.fatal "unexpected prototype for malloc"
          in
          let range =
            Logic_const.trange
              (Some (Cil.lzero ()),
               Some (Logic_const.tvar (Cil.cvar_to_lvar prm)))
          in
          let typ = Ctype Cil.charPtrType in
          let base =
            Logic_const.term
              (TCastE(Cil.charPtrType, Check, Logic_const.tresult Cil.charPtrType)) typ
          in
          let alloc =
            Logic_const.new_identified_term
              (Logic_const.term (TBinOp(PlusPI,base,range)) typ)
          in
          let behav =
            {
              b_name = Cil.default_behavior_name;
              b_assumes = [];
              b_requires = [];
              b_extended = [];
              b_assigns = Writes [];
              b_allocation = FreeAlloc ([], [alloc]);
              b_post_cond = []
            }
          in
          let spec = { (empty_funspec ()) with spec_behavior = [behav] } in
          Globals.Functions.replace_by_declaration
            spec f Location.unknown;
          let kf = Globals.Functions.get f in
          Annotations.register_funspec ~emitter:Emitters.jessie kf;
          f

      let free () =
        try
          Kernel_function.get_vi (Globals.Functions.find_by_name "free")
        with Not_found ->
          let params = Some ["ptr", voidPtrType, []] in
          let f =
            findOrCreateFunc
              (Ast.get ()) "free" (TFun (voidType, params, false, []))
          in
          let prm =
            try
              List.hd (Cil.getFormalsDecl f)
            with Not_found | Invalid_argument _ ->
              Console.fatal "unexpected prototype for free"
          in
          let frees =
            Logic_const.new_identified_term
              (Logic_const.tvar (Cil.cvar_to_lvar prm))
          in
          let behav =
            {
              b_name = Cil.default_behavior_name;
              b_assumes = [];
              b_post_cond = [];
              b_requires = [];
              b_extended = [];
              b_allocation = FreeAlloc([frees], []);
              b_assigns = Writes []
            }
          in
          let spec = { (empty_funspec ()) with spec_behavior = [behav] } in
          Globals.Functions.replace_by_declaration
            spec f Location.unknown;
          let kf = Globals.Functions.get f in
          Annotations.register_funspec ~emitter:Emitters.jessie kf;
          f
    end

    module Variable =
    struct
      type t = var t'

      let of_varinfo vi =
        try
          Some (ignore (Globals.Vars.get_astinfo vi : string * localisation); vi)
        with
        | Not_found -> None

      let of_varinfo_exn vi =
        try
          ignore (Globals.Vars.get_astinfo vi : string * localisation); vi
        with
        | Not_found -> invalid_arg "Ast.Vi.Function.of_vi_exn: no function for varinfo"

      let pseudo =
        let counter = ref 0 in
        function ty ->
          incr counter;
          let name = "@" ^ (string_of_int !counter) in
          makeVarinfo ~source:false (* global = *) false (* formal = *) false name ty
    end
  end

  module Term =
  struct
    type t = term

    let is_base_addr t =
      match (stripTermCasts t).term_node with
      | Tbase_addr _ -> true
      | _ -> false

    let mk ?name:(term_name=[]) ~typ:term_type ~loc:term_loc term_node =
      {
        term_node;
        term_loc;
        term_type;
        term_name
      }

    let mk_loc ?name:(term_name=[]) ~typ:term_type ~loc term_node =
      {
        term_node;
        term_loc = map_pair Loc.to_position loc;
        term_type;
        term_name
      }

    let of_var v =
      let lv = cvar_to_lvar v in
      match lv.lv_type with
      | Ctype typ when isArrayType typ ->
        mk ~typ:(Ctype (TPtr (element_type typ, []))) ~loc:v.vdecl @@ TStartOf (TVar lv, TNoOffset)
      | _ ->
        mk ~typ:lv.lv_type ~loc:v.vdecl @@ TLval(TVar lv,TNoOffset)

    (* Force conversion from terms to expressions by returning, along with
     * the result, a map of the sub-terms that could not be converted as
     * a map from fresh variables to terms or term left-values. *)

    let rec typ_of_logic_c_type =
      function
      | Ctype typ -> typ
      | Linteger -> TInt (ILongLong, []) (* TODO: to have an unlimited integer type
                                            in the logic interpretation *)
      | Lreal -> TFloat (FLongDouble, []) (* TODO: handle reals, not floats... *)
      | Ltype ({ lt_name = name }, []) when name = Utf8_logic.boolean  ->
        TInt (ILongLong, [])
      | Ltype ({ lt_name = "set" }, [t]) -> typ_of_logic_c_type t
      | Ltype _ | Lvar _ | Larrow _ -> raise Exit

    module Env =
      struct
        type t =
          {
            term_lhosts : term_lhost Varinfo.Map.t;
            terms : term Varinfo.Map.t;
            vars : logic_var Varinfo.Map.t;
          }

        let empty =
          {
            term_lhosts = Varinfo.Map.empty;
            terms = Varinfo.Map.empty;
            vars = Varinfo.Map.empty
          }

        let dummy_type =
          let ci =
            mkCompInfo true (Name.unique "dummy_type") (fun _ -> ["charM", charType, None, [], Location.unknown]) []
          in
          TPtr (TComp (ci, empty_size_cache (), []), [])

        let merge env1 env2 =
          {
            term_lhosts =
              Varinfo.Map.fold
                Varinfo.Map.add
                env1.term_lhosts
                env2.term_lhosts;
            terms = Varinfo.Map.fold Varinfo.Map.add env1.terms env2.terms;
            vars = Varinfo.Map.fold Varinfo.Map.add env1.vars env2.vars
          }

        let add_term env t =
          (* Precise the type when possible *)
          let ty =
            match t.term_type with
            | Ctype ty -> ty
            | Ltype ({ lt_name = "set" }, [Ctype ty]) -> ty
            | _ -> dummy_type
          in
          let v = Vi.Variable.pseudo ty in
          let env = { env with terms = Varinfo.Map.add v t env.terms } in
          Lval (Var v, NoOffset), env

        let add_var env v =
          let ty =
            match v.lv_type with
            | Ctype ty -> ty
            | _ -> Console.fatal "Ast.Term.Env.add_var: not a C-typed var: %a" Printer.pp_logic_var v
          in
          let pv = Vi.Variable.pseudo ty in
          let env = { env with vars = Varinfo.Map.add pv v env.vars } in
          Var pv, env

        let add_lhost env lhost =
          let v = Vi.Variable.pseudo dummy_type in
          let env = { env with term_lhosts = Varinfo.Map.add v lhost env.term_lhosts } in
          Var v, env

        let add_result env ty =
          let pv = Vi.Variable.pseudo ty in
          let env =
            { env with term_lhosts =
                         Varinfo.Map.add pv (TResult ty) env.term_lhosts }
          in
          Var pv, env
      end

    let rec to_exp_env t =
      let loc = t.term_loc in
      let const_of_lconst =
        function
        | Integer (i, so) when Integer.(le min_int64 i && le i max_int64) ->
          CInt64 (i, ILongLong, so)
        | LStr s -> CStr s
        | LWStr il -> CWStr il
        | LChr c -> CChr c
        | LEnum ei -> CEnum ei
        | LReal _
        | Integer _ -> raise Exit
      in
      let try_ f = try f () with Exit -> Env.add_term Env.empty t in
      let e, env =
        match t.term_node with
        | TLval tlv ->
          (match Logic_utils.unroll_type t.term_type with
           | Ctype (TArray _) -> Env.add_term Env.empty t
           | _ -> let lv, env = lval_to_lval_env tlv in Lval lv, env)
        | TAddrOf tlv ->
          let lv, env = lval_to_lval_env tlv in AddrOf lv, env
        | TStartOf tlv ->
          let lv, env = lval_to_lval_env tlv in StartOf lv, env
        | TSizeOfE t' ->
          let e, env = to_exp_env t' in SizeOfE e, env
        | TAlignOfE t' ->
          let e, env = to_exp_env t' in AlignOfE e, env
        | TUnOp (unop, t') ->
          try_ @@ fun () ->
          let typ = typ_of_logic_c_type t.term_type in
          let e, env = to_exp_env t' in
          UnOp (unop, e, typ), env
        | TBinOp (binop, t1, t2) ->
          try_ @@ fun () ->
          let e1, env1 = to_exp_env t1 in
          let e2, env2 = to_exp_env t2 in
          let env = Env.merge env1 env2 in
          BinOp (binop, e1, e2, typ_of_logic_c_type t.term_type), env
        | TSizeOfStr string -> SizeOfStr string, Env.empty
        | TLogic_coerce (Linteger, t) ->
          let e, env = to_exp_env t in
          CastE (TInt (IInt, [Attr ("integer", [])]), Check, e), env
        | TLogic_coerce (Lreal, t) ->
          let e, env = to_exp_env t in
          CastE (TFloat (FFloat, [Attr ("real",[])]), Check, e), env
        | TCastE (ty, oft, t') ->
          let e, env = to_exp_env t' in CastE (ty, oft, e), env
        | TAlignOf ty -> AlignOf ty, Env.empty
        | TSizeOf ty -> SizeOf ty, Env.empty
        | TConst c ->
          try_ @@ fun () ->
          Const (const_of_lconst c), Env.empty
        | Tapp _ | TDataCons _ | Tif _ | Tpif _ | Tat _ | Tbase_addr _ | TOffsetOf _
        | Toffset _ | Toffset_max _ | Toffset_min _
        | Tblock_length _ | Tnull | TCoerce _ | TCoerceE _ | TUpdate _
        | Tlambda _ | Ttypeof _ | Ttype _ | Tcomprehension _
        | Tunion _ | Tinter _ | Tempty_set | Trange _ | Tlet _
        | TLogic_coerce _ ->
          Env.add_term Env.empty t
      in
      let e, env =
        let rec is_safe =
          function
          | Lval (Mem e, _) when not (isPointerType @@ typeOf e) -> false
          | Lval (Mem e, _) -> is_safe e.enode
          | _ -> true
        in
        if is_safe e then e, env
        else Env.add_term Env.empty t
      in
      let info_if_needed t e =
        let info () = new_exp ~loc @@ Info (e, exp_info_of_term t) in
        if t.term_name = [] then
          match t.term_type, typeOf e with
          | Ctype t1, t2 when Typ.equal t1 t2 -> e
          | _ -> info ()
        else info ()
      in
      info_if_needed t @@ new_exp ~loc e, env

    and lval_to_lval_env (lhost, toff) =
      let lhost, env1 = lhost_to_lhost_env lhost in
      let off, env2 = offset_to_offset_env toff in
      let env = Env.merge env1 env2 in
      (lhost, off), env

    and lhost_to_lhost_env lhost =
      match lhost with
      | TVar v ->
        begin match v.lv_origin with
        | Some v -> Var v, Env.empty
        | None ->
          begin match v.lv_type with
          | Ctype _ty -> Env.add_var Env.empty v
          | _ -> Env.add_lhost Env.empty lhost
          end
        end
      | TMem t ->
        let e, env = to_exp_env t in
        Mem e, env
      | TResult ty -> Env.add_result Env.empty ty

    and offset_to_offset_env =
      function
      | TNoOffset -> NoOffset, Env.empty
      | TField (fi, toff) ->
        let off, env = offset_to_offset_env toff in
        Field (fi, off), env
      | TModel _ ->
        invalid_arg "Ast.Term.offset_to_offset_env: model field"
      | TIndex (t, toff) ->
        let e, env1 = to_exp_env t in
        let off, env2 = offset_to_offset_env toff in
        let env = Env.merge env1 env2 in
        Index (e, off), env

    (* Force back conversion from expression to term, using the environment
     * constructed during the conversion from term to expression. It expects
     * the top-level expression to be wrapped into an Info, as well as every
     * top-level expression that appears under a left-value. *)

    let rec of_exp_env (e, env) =
      let rec of_exp_env' (e, env) =
        let einfo =
          match e.enode with
          | Info (_e, einfo) -> einfo
          | _ -> { exp_type = Ctype (typeOf e); exp_name = [] }
        in
        let tnode =
          match (stripInfo e).enode with
          | Info _ -> assert false (* stripInfo *)
          | Const c -> TConst (Logic_utils.constant_to_lconstant c)
          | Lval (Var v, NoOffset as lv) ->
            begin try
              (Varinfo.Map.find v env.Env.terms).term_node
            with Not_found ->
              TLval (lval_of_lval_env (lv, env))
            end
          | Lval lv -> TLval (lval_of_lval_env (lv,  env))
          | SizeOf ty -> TSizeOf ty
          | SizeOfE e -> TSizeOfE (of_exp_env' (e, env))
          | SizeOfStr s -> TSizeOfStr s
          | AlignOf ty -> TAlignOf ty
          | AlignOfE e -> TAlignOfE (of_exp_env' (e, env))
          | UnOp (op, e, _) -> TUnOp (op, of_exp_env' (e, env))
          | BinOp (op, e1, e2, _) ->
            TBinOp (op,
                    of_exp_env' (e1, env),
                    of_exp_env' (e2, env))
          | CastE (TInt (IInt, [Attr ("integer", [])]), _, e) ->
            TLogic_coerce (Linteger, of_exp_env' (e, env))
          | CastE (TFloat (FFloat, [Attr ("real", [])]), _, e) ->
            TLogic_coerce (Lreal, of_exp_env' (e, env))
          | CastE (ty, oft, e) -> TCastE (ty, oft, of_exp_env' (e, env))
          | AddrOf lv -> TAddrOf (lval_of_lval_env (lv, env))
          | StartOf lv -> TStartOf (lval_of_lval_env (lv, env))
        in
        term_of_exp_info e.eloc tnode einfo
      in
      of_exp_env' (e, env)

    and offset_of_offset_env (off, env) =
      match off with
      | NoOffset -> TNoOffset
      | Field (fi, off) ->
        TField (fi, offset_of_offset_env (off, env))
      | Index (idx, off) ->
        TIndex (of_exp_env (idx, env),
                offset_of_offset_env (off, env))

    and lhost_of_lhost_env (lhost, env) =
      match lhost with
      | Var v ->
        begin try
          let logv = Varinfo.Map.find v env.Env.vars in
          logv.lv_type <- Ctype v.vtype;
          TVar logv
        with Not_found ->
          try Varinfo.Map.find v env.Env.term_lhosts
          with Not_found -> TVar (cvar_to_lvar v)
        end
      | Mem e -> TMem (of_exp_env (e, env))

    and lval_of_lval_env ((host, off), env) =
      lhost_of_lhost_env (host, env),
      offset_of_offset_env (off, env)

    let rec of_exp e =
      let tnode =
        match (stripInfo e).enode with
        | Info _ -> assert false (* stripInfo *)
        | Const c -> TConst (Logic_utils.constant_to_lconstant c)
        | Lval lv -> TLval (lval_of_lval lv)
        | SizeOf ty -> TSizeOf ty
        | SizeOfE e -> TSizeOfE (of_exp e)
        | SizeOfStr s -> TSizeOfStr s
        | AlignOf ty -> TAlignOf ty
        | AlignOfE e -> TAlignOfE (of_exp e)
        | UnOp (op, e, _) -> TUnOp (op, of_exp e)
        | BinOp (op, e1, e2, _) ->
          TBinOp (op, of_exp e1, of_exp e2)
        | CastE (ty, oft, e) -> TCastE (ty, oft, of_exp e)
        | AddrOf lv -> TAddrOf (lval_of_lval lv)
        | StartOf lv -> TStartOf (lval_of_lval lv)
      in
      {
        term_node = tnode;
        term_loc = e.eloc;
        term_type = Ctype (typeOf e);
        term_name = [];
      }

    and offset_of_offset =
      function
      | NoOffset -> TNoOffset
      | Field (fi, off) ->
        TField (fi, offset_of_offset off)
      | Index (idx, off) ->
        TIndex (of_exp idx,
                offset_of_offset off)

    and lhost_of_lhost =
      function
      | Var v -> TVar (cvar_to_lvar v)
      | Mem e -> TMem (of_exp e)

    and lval_of_lval (host, off) =
      lhost_of_lhost host,
      offset_of_offset off
  end

  module Predicate =
  struct
    type t = predicate

    let mk ?name:(pred_name=[]) ~loc:pred_loc pred_content =
      {
        pred_name;
        pred_loc;
        pred_content
      }

    let rec of_exp_exn e =
      let pnode =
        match (stripInfo e).enode with
        | Info _ ->
          Console.fatal "Ast.Predicate.of_exp_exn: Info is unsupported (shoud not happen): %a" Printer.pp_exp e
        | Const c ->
          begin match possible_value_of_integral_const c with
          | Some i -> if Integer.equal i Integer.zero then Pfalse else Ptrue
          | None -> Console.fatal "Ast.Predicate.of_exp_exn: couldn't handle the constant: %a" Printer.pp_exp e
          end
        | UnOp (LNot, e, _) -> Pnot (of_exp_exn e)
        | BinOp (LAnd, e1, e2, _) ->
          Pand (of_exp_exn e1, of_exp_exn e2)
        | BinOp (LOr, e1, e2, _) ->
          Por (of_exp_exn e1, of_exp_exn e2)
        | BinOp (op, e1, e2, _) ->
          let rel =
            match op with
            | Lt -> Rlt
            | Gt -> Rgt
            | Le -> Rle
            | Ge -> Rge
            | Eq -> Req
            | Ne -> Rneq
            | _ -> Console.fatal "Ast.Predicate.of_exp_exn: couldn't handle binop: %a" Printer.pp_binop op
          in
          Prel (rel, Term.of_exp e1, Term.of_exp e2)
        | Lval _ | CastE _ | AddrOf _ | StartOf _ | UnOp _
        | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
          Console.fatal "Ast.Predicate.of_exp_exn: non-predicate expression: %a" Printer.pp_exp e
      in
      { pred_name = []; pred_loc = e.eloc; pred_content = pnode }
  end

  module Code_annotation =
  struct
    type t = code_annotation

    let of_exp_exn e =
      Logic_const.new_code_annotation (AAssert ([], Predicate.of_exp_exn e))
  end

  module Offset =
  struct
    type t = offset

    let is_last =
      function
      | NoOffset -> true
      | Field (_fi, NoOffset) -> true
      | Field (_fi, _) -> false
      | Index (_e, NoOffset) -> true
      | Index (_e, _) -> false

    (* Transform an index on a multi-dimensional array into an index on the
     * same array that would be flattened to a single dimensional array.
    *)
    let rec flatten ~typ =
      function
      | Index (idx1, (Index (idx2, _off) as suboff)) ->
        let subty = direct_element_type typ in
        let siz = array_size subty in
        begin match flatten ~typ:subty suboff with
        | Index (idx, off) ->
          let mulidx =
            new_exp
              ~loc:idx2.eloc @@
              BinOp (Mult Check, idx1, Exp.const siz, intType)
          in
          (* Keep info at top-level for visitors on terms that where
           * translated to expressions. Those expect these info when
           * translating back to term.
           *)
          let addidx =
            map_under_info
              (fun e ->
                 new_exp ~loc:e.eloc @@ BinOp (PlusA Check, mulidx, idx, intType))
              idx1
          in
          Index (addidx, off)
        | off -> Console.fatal "Ast.Offset.flatten: unexpected offset: %a" Printer.pp_offset off
        end
      | Index (idx1, NoOffset) as off ->
        let subty = direct_element_type typ in
        if isArrayType subty then
          let siz = array_size subty in
          (* Keep info at top-level *)
          let mulidx =
            map_under_info
              (fun e ->
                 new_exp
                   ~loc:e.eloc @@
                   BinOp (Mult Check, idx1, Exp.const siz, intType))
              idx1
          in
          Index (mulidx, NoOffset)
        else
          off
      | off -> off
  end

  module Instr =
  struct
    type t = instr

    let alloc_singleton ~lvar:v ~typ:ty ~loc =
      let callee = evar ~loc @@ Vi.Function.malloc () in
      let arg = sizeOf ~loc ty in
      Call (Some (Var v, NoOffset), callee, [arg], loc)

    let alloc_array ~lvar:v ~typ:ty ~size:num ~loc =
      let callee = evar ~loc @@ Vi.Function.malloc () in
      let arg =
        Exp.const @@
          Integer.of_int64 @@ Int64.mul num @@ Int64.of_int @@ bytesSizeOf ty
      in
      Call (Some (Var v, NoOffset), callee, [arg], loc)

    let free ~loc v =
      let callee = evar ~loc @@ Vi.Function.free () in
      let arg = evar ~loc v in
      Call (None, callee, [arg], loc)
  end

  module Stmt =
  struct
    type t = stmt

    let alloc_singleton ~lvar ~typ ~loc = mkStmt @@ Instr (Instr.alloc_singleton ~lvar ~typ ~loc)
    let alloc_array ~lvar ~typ ~size ~loc =
      mkStmt @@ Instr (Instr.alloc_array ~lvar ~typ ~size ~loc)
    let free ~loc v = mkStmt @@ Instr (Instr.free ~loc v)
  end
end

module Type =
struct

  type composite
  type integral
  type ref

  type 'a t = typ
  type 'a t' = 'a t

  module Logic_c_type =
  struct
    type t = logic_type

    let of_logic_type =
      function
      | Ctype _
      | Ltype ({ lt_name = "set" }, [_]) as ty -> Some ty
      | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> None

    let of_logic_type_exn t =
      of_logic_type t |>
      function
      | Some ty -> ty
      | None -> Console.fatal "Logic_c_type.of_logic_type_exn: not a logic c type: %a" Printer.pp_logic_type t

    let rec map_default ~default ~f =
      function
      | Ctype typ -> f typ
      | Ltype ({ lt_name = "set" }, [t]) -> map_default ~default ~f t
      | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> default

    let rec map ~f =
      function
      | Ctype typ -> f typ
      | Ltype ({ lt_name = "set" }, [t]) -> map ~f t
      | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ as ty ->
        Console.fatal "map_logic_c_type_exn: unexpected non-C type: %a" Printer.pp_logic_type ty

    let get = map ~f:Fn.id

    let is_c = Option.is_some % of_logic_type

    let typ = Option.map ~f:get % of_logic_type
  end

  module Ref =
  struct

    (* Reference type *)

    type t = ref t'

    (* We introduce a reference type, that is different from the C pointer or
     * array type. It is a direct translation in C of the Jessie bounded pointer
     * type, where the lower/upper bounds that can be safely accessed are
     * statically known. To avoid introducing a new type, we reuse the existing
     * C pointer type, with an attribute "arrlen" to give the size.
     * Then, we use it as a regular pointer type. E.g., we allow dynamic allocation
     * of such references:
     *     r = (TRef(T)) (malloc (sizeof(T)));
     * and usual dereference:
     *     T t = *r;
     * Another advantage is it should be working fine with [typeOf], [typeOfLval],
     * [pointed_type] and similar functions.
     *
     * As a result of this transformation, all allocation/releases of memory
     * on a reference type do implicitly allocate/release the fields of reference
     * type. It will be translated in Jessie in various alloc/free statements. *)

    let singleton ~msg:_ elemty =
      (* Define the same arguments as for [mkTRefArray] *)
      let size = Ast.Exp.const Integer.one and attr = [] in
      (* Do the same as in [mkTRefArray] *)
      let siz = expToAttrParam size in
      let attr = addAttribute (Attr (Name.Attr.arraylen, [siz])) attr in
      (* Avoid creating an array for single pointed elements that do not
       * originate in a C array, to avoid having to access to the first
       * element everywhere.  *)
      TPtr (elemty, attr)

    let array ~size ?(attrs=[]) typ =
      (* Check the array size is of a correct form *)
      ignore (lenOfArray64 (Some size));
      let siz = expToAttrParam size in
      let attrs = addAttribute (Attr (Name.Attr.arraylen, [siz])) attrs in
      (* Make the underlying type an array so that indexing it is still valid C. *)
      TPtr (TArray (typ, Some size, empty_size_cache (), []), attrs)

    let size ty =
      match findAttribute Name.Attr.arraylen (typeAttrs ty) with
      | [AInt i] -> Integer.to_int64 i
      | [ACons (_, [])] -> 0L
      | _ -> Console.fatal "Type.Ref.size: non-reference type: %a" Printer.pp_typ ty

    let of_typ ty =
      match findAttribute Name.Attr.arraylen (typeAttrs ty) with
      | [AInt _]
      | [ACons (_, [])] -> Some ty
      | _ -> None

    let of_typ_exn ty =
      match of_typ ty with
      | Some ty -> ty
      | None -> Console.fatal "Type.Ref.of_typ_exn: non-reference type: %a" Printer.pp_typ ty

    let typ ty =
      match of_typ ty with
      | Some ty when isPointerType ty -> pointed_type ty
      | _ -> Console.fatal "Type.Ref.typ: non-reference type: %a" Printer.pp_typ ty

    let is_ref ty =
      isPointerType ty && hasAttribute Name.Attr.arraylen (typeAttrs ty)

    let is_array_ref ty =
      is_ref ty && isArrayType (unrollType (direct_pointed_type ty))

    let is_array ty =
      isArrayType (unrollType (direct_pointed_type ty))

    let of_array_exn ty =
      let rec reftype ty =
        if isArrayType ty then
          let typ = reftype (direct_element_type ty) in
          let size = Ast.Exp.const (direct_array_size ty) in
          array ~size typ
        else ty
      in
      if not (isArrayType ty) then
        invalid_arg "Type.Ref.of_array_exn: non-array type";
      reftype ty
  end

  module Composite =
  struct

    type t = composite t'

    let of_typ ty =
      match unrollType ty with
      | TComp _ -> Some ty
      | _ -> None

    let of_typ_exn ty =
      match unrollType ty with
      | TComp _ -> ty
      | _ -> invalid_arg "Type.Composite.of_typ_exn: non-composite type"

    let unique_field_exn ty =
      match unrollType ty with
      | TComp (compinfo, _, _) ->
        begin match compinfo.cfields with
        | [content_fi] -> content_fi
        | _ -> Console.fatal "get_unique_field_exn: type %a has no unique field" Printer.pp_typ ty
        end
      | ty -> Jessie_options.fatal "get_unique_field_exn: non-composite type: %a" Printer.pp_typ ty

    let compinfo_cname =
      function
      | TComp (ci, _, _) -> ci.cname
      | ty -> Console.fatal "get_compinfo_cname_exn: non-composite type: %a" Printer.pp_typ ty

    let compinfo =
      function
      | TComp (ci, _, _) -> ci
      | ty -> Jessie_options.fatal "get_compinfo_exn: non-composite type: %a" Printer.pp_typ ty

    module Ci =
    struct

      type t = compinfo

      module Struct =
      struct

        type t = compinfo

        let of_ci ci = if ci.cstruct then Some ci else None

        let of_ci_exn ci =
          if ci.cstruct then ci
          else Console.fatal "Ci.Struct.of_ci_exn: not a struct compinfo: %s" (compFullName ci)

        (* Wrappers on [mkCompInfo] that update size/offset of fields *)

        let empty stname =
          mkCompInfo true stname (fun _ -> []) []

        let singleton ?(padding=0) ~sname ~fname typ =
          let compinfo =
            mkCompInfo true sname
              (fun _ -> [fname, typ, None, [Attr (Name.Attr.noembed, [])], CurrentLoc.get ()]) []
          in
          let fi = unique_field_exn @@ TComp (compinfo, empty_size_cache (), []) in
          fi.fsize_in_bits <- Some (bitsSizeOf typ);
          fi.foffset_in_bits <- Some 0;
          fi.fpadding_in_bits <- Some padding;
          compinfo
      end

      let size ci =
        if ci.cdefined then Some (bitsSizeOf @@ TComp (ci, empty_size_cache (), []))
        else None

      let fill_jessie_fields ci =
        let basety = TComp (ci, empty_size_cache (), []) in
        let field fi nextoff =
          let offset_in_bits, size_in_bits = bitsOffset basety (Field (fi, NoOffset)) in
          let padding_in_bits = nextoff - offset_in_bits - size_in_bits in
          if padding_in_bits < 0 then
            Console.unsupported
              "assertion failed while computing paddings in composite type %s: \
               the sum of the offset and size of the field %s (%d + %d) is *larger* than \
               the offset of the next field (%d): cannot handle a negative padding:@[<hov 2>%a@]"
              (compFullName ci)
              fi.forig_name
              offset_in_bits
              size_in_bits
              nextoff
              (pp_print_list
                 ~pp_sep:(fun f () -> fprintf f ";@\n")
                 (fun f fi ->
                    let o, s = bitsOffset basety (Field (fi, NoOffset)) in
                    fprintf f "%s : %d @@ %d" fi.forig_name s o))
              ci.cfields;
          fi.fsize_in_bits <- Some size_in_bits;
          fi.foffset_in_bits <- Some offset_in_bits;
          fi.fpadding_in_bits <- Some padding_in_bits;
          if ci.cstruct then offset_in_bits
          else nextoff (* union type *)
        in
        begin try
          ignore (List.fold_right field ci.cfields (bitsSizeOf basety))
        with
        | SizeOfError (s, typ) ->
          Console.warning
            "SizeOfError occurred when computing bit offsets in composite type %s: %s (in type %a)"
            (compFullName ci)
            s
            Printer.pp_typ typ
        end

      let padding_field =
        let padding_type = intType in
        fun ~fsize_in_bits ci ->
          let fsize_in_bits = Some fsize_in_bits in
          {
            fcomp = ci;
            forig_name = "";
            fname = Name.unique "padding";
            ftype = padding_type;
            fbitfield = fsize_in_bits;
            fattr = [Attr ("const", []); Attr (Name.Attr.padding, []); Attr (Name.Attr.packed, [])];
            floc = Location.unknown;
            faddrof = false;
            fsize_in_bits;
            foffset_in_bits = None;
            fpadding_in_bits = None
          }

      let fix_size ?original_size ci =
        let current_size = size ci in
        match original_size, current_size with
        | Some original_size, Some current_size ->
          let current_size =
            if current_size > original_size then begin
              ci.cattr <- Attr (Name.Attr.packed, []) :: ci.cattr;
              Option.value_fatal ~in_:"fix_size" @@ size ci
            end else current_size
          in
          List.iter (fun fi -> fi.foffset_in_bits <- None) ci.cfields;
          let warn action =
            Console.debug "Fixing size of composite [%s] by %s" (compFullName ci) action
          in
          if current_size < original_size then begin
            warn "padding";
            ci.cfields <- ci.cfields @ [padding_field ~fsize_in_bits:(original_size - current_size) ci]
          end else if current_size > original_size then begin
            warn "shrinking";
            let remaining_size_fix =
              List.fold_left
                (fun size_fix fi ->
                   if size_fix > 0 &&
                      not (hasAttribute Name.Attr.embedded fi.fattr) &&
                      hasAttribute Name.Attr.padding fi.fattr
                   then
                     let bitsize =
                       match fi.fsize_in_bits with
                       | Some s -> s
                       | None -> failwith "fix_size_of_composite: invalid padding field"
                     in
                     let available_fix = min size_fix bitsize in
                     fi.fsize_in_bits <- Some (bitsize - available_fix);
                     fi.fbitfield <- fi.fsize_in_bits;
                     size_fix - available_fix
                   else
                     size_fix)
                (current_size - original_size)
                (List.rev ci.cfields)
            in
            if (remaining_size_fix > 0) then
              let composite_name = compFullName ci in
              let original_name = if ci.corig_name <> "" then ci.corig_name else "<anonymous>" in
              let original_size, current_size = Pair.map (fun s -> s lsr 3) (original_size, current_size) in
              let pointer_size = theMachine.theMachine.sizeof_ptr in
              let empty_members =
                List.flatten @@
                List.map
                  (fun { ftype } ->
                     let check_type ty =
                       let ci = compinfo @@ unrollType ty in
                       if size ci = Some 0 then [ci] else []
                     in
                     if isStructOrUnionType ftype then
                       check_type ftype
                     else if Ref.is_ref ftype && isStructOrUnionType (pointed_type ftype) then
                       check_type (pointed_type ftype)
                     else [])
                  ci.cfields
                |>
                function
                | [] -> "."
                | empty_members ->
                  Printf.sprintf " or to one of its empty composite members (i.e. %s)"
                    (String.concat ", " @@ List.map compFullName empty_members)
              in
              Console.unsupported
                "Couldn't maintain the size of %s (%s, size is %d). \
                 The size has grown to %d during the last transformation, \
                 but there's no padding (or unused fields) to use for shrinking. \
                 One possible cause of the problem \
                 is structure or array-to-pointer retyping, where the size of the retyped structure/array \
                 was initially less than the size of a pointer (%d). \
                 One possible solution is to add one or several unused fields to the %s%s"
                composite_name original_name original_size current_size pointer_size composite_name empty_members
            else
              assert (remaining_size_fix = 0)
          end
        | _ -> ()

      let proper_fields ci = List.filter (fun fi -> not @@ hasAttribute Name.Attr.padding fi.fattr) ci.cfields
    end

    module Struct =
    struct
      type t = typ
      let void_wrapper = ref None
      let void () =
        match !void_wrapper with
        | Some wrapper -> wrapper
        | None -> Console.fatal "Type.Composite.Struct.void: called before normalization"

      let char_wrapper = ref None
      let char () =
        match !char_wrapper with
        | Some wrapper -> wrapper
        | None -> Console.fatal "Type.Composite.Struct.char: called before normalization"

      let of_typ ty =
        match unrollType ty with
        | TComp ({ cstruct = true }, _, _) ->
          Some ty
        | _ -> None

      let is_struct ty =
        match of_typ ty with
        | Some _ -> true
        | None -> false

      let of_typ_exn ty =
        match of_typ ty with
        | Some ty -> ty
        | None -> Console.fatal "Type.Composite.Struct.of_ty_exn: called on non-struct"

      let init_void wrapper =
        match !void_wrapper with
        | Some _ -> Console.fatal "Type.Composite.Struct.init_void: called after initilization"
        | None ->
          match wrapper with
          | TComp ({ cstruct = true }, _, _) ->
            void_wrapper := Some wrapper
          | _ -> Console.fatal "Type.Composite.Struct.init_void: called on non-struct"

      let init_char wrapper =
        match !char_wrapper with
        | Some _ -> Console.fatal "Type.Composite.Struct.init_char: called after initilization"
        | None ->
          match wrapper with
          | TComp ({ cstruct = true }, _, _) ->
            char_wrapper := Some wrapper
          | _ -> Console.fatal "Type.Composite.Struct.init_char: called on non-struct"
    end
  end

  let promote_argument_type arg_type =
    match unrollType arg_type with
    | TVoid _                            -> voidType
    | TInt (k,_) when rank k < rank IInt ->
      if intTypeIncluded k IInt then       intType
      (* This may happen when char or short have the same size as int *)
      else                                 uintType
    | TInt (k, _)                        -> TInt(k, [])
    | TFloat (FFloat, _)                 -> doubleType
    | TFloat (k, _)                      -> TFloat (k, [])
    | TPtr (t, _) | TArray (t, _, _, _)  -> TPtr (t, [])
    | TFun _ as t                        -> TPtr (t, [])
    | TComp (ci, _, _)                   -> TComp (ci, { scache = Not_Computed }, [])
    | TEnum (ei, _)                      -> TEnum (ei, [])
    | TBuiltin_va_list _                 -> Console.fatal ~current:true "promote_argument_type: variadic arguments"
    | TNamed _                           -> assert false (* unrollType *)

  let size_in_bits_exn ty =
    let open! Jessie_integer in
    match unrollType ty with
    | TPtr _ -> Int64.of_int (bitsSizeOf ty)
    | TArray _ -> invalid_arg "Type.size_in_bits_exn: array type" (* Shold be removed by translation *)
    | TFun _ -> Console.unsupported "Function pointer type %a is not supported" Printer.pp_typ ty
    | TNamed _ -> assert false (* Removed by call to [unrollType] *)
    | TComp (compinfo, _, _) ->
      let size_from_field fi =
        match fi.foffset_in_bits, fi.fsize_in_bits, fi.fpadding_in_bits with
        | Some off, Some siz, Some padd ->
          Int64.of_int off + Int64.of_int siz + Int64.of_int padd
        | _ -> invalid_arg "Type.size_in_bits_exn: fieldinfo field not computed"
      in
      if compinfo.cstruct then
        match List.rev compinfo.cfields with
        | [] -> 0L
        | fi :: _ -> size_from_field fi
      else
        List.fold_left max 0L (List.map size_from_field compinfo.cfields)
    | TEnum _ | TVoid _ | TInt _ | TFloat _ | TBuiltin_va_list _ ->
      Int64.of_int (bitsSizeOf ty)

  module Integral =
  struct

    type t = integral t'

    let of_typ ty =
      match unrollType ty with
      | TInt _
      | TEnum _ -> Some ty
      | _ -> None

    let of_typ_exn ty =
      match unrollType ty with
      | TInt _
      | TEnum _ -> ty
      | _ -> invalid_arg "Type.Integral.of_typ_exn: non-integral type"

    (* Type for ghost variables until integer is a valid type for ghosts. *)
    let almost_unbound = TInt (ILongLong, [])

    module IKind =
    struct
      type t = ikind

      let size_in_bytes =
        function
        | IBool -> Console.unsupported "Type.Integral.IKind.size_in_bytes: IBool"
        | IChar | ISChar | IUChar -> 1 (* Cil assumes char is one byte *)
        | IInt | IUInt -> theMachine.theMachine.sizeof_int
        | IShort | IUShort -> theMachine.theMachine.sizeof_short
        | ILong | IULong -> theMachine.theMachine.sizeof_long
        | ILongLong | IULongLong -> theMachine.theMachine.sizeof_longlong
    end

    let int ?(attrs=[]) ikind = TInt (ikind, attrs)

    let is_signed = isSignedInteger

    let size_in_bytes ty =
      match unrollType ty with
      | TInt (IBool, _attr) -> (* TODO *)
        Console.unsupported "Type.Integral.size_in_bytes: IBool"
      | TInt (ik, _attr) -> IKind.size_in_bytes ik
      | TEnum ({ ekind = IBool }, _) ->
        Console.unsupported "Type.Integral.size_in_bytes: IBool"
      | TEnum (ei, _) -> IKind.size_in_bytes ei.ekind
      | ty -> Console.fatal "Type.Integral.size_in_bytes: non-integral type: %a" Printer.pp_typ ty

    let size_in_bits = (( * ) 8) % size_in_bytes

    let min_value ?bitsize ty =
      let min_of signed size_in_bytes =
        if signed
        then Integer.(neg @@ power_int_positive_int 2 @@ (bitsize |? 8 * size_in_bytes) - 1)
        else Integer.zero
      in
      match unrollType ty with
      | TInt (IBool, _attr) -> Integer.zero
      | TInt (ik, _attr) ->
        min_of (isSigned ik) (IKind.size_in_bytes ik)
      | TEnum ({ ekind = IBool }, _)-> Integer.zero
      | TEnum (e, _) ->
        let ik = e.ekind in
        min_of (isSigned ik) (IKind.size_in_bytes ik)
      | ty -> Console.fatal "Type.Integral.min_value: non-integral type: %a" Printer.pp_typ ty

    let max_value ?bitsize ty =
      let max_of signed size_in_bytes =
        let nbits = bitsize |? 8 * size_in_bytes in
        Integer.(pred @@ power_int_positive_int 2 @@ if signed then nbits - 1 else nbits)
      in
      match unrollType ty with
      | TInt (IBool, _attr) -> Integer.one
      | TInt (ik, _attr) ->
        max_of (isSigned ik) (IKind.size_in_bytes ik)
      | TEnum ({ ekind = IBool }, _) -> Integer.one
      | TEnum (e, _) ->
        let ik = e.ekind in
        max_of (isSigned ik) (IKind.size_in_bytes ik)
      | ty -> Console.fatal "Type.Integral.max_value: non-integral type: %a" Printer.pp_typ ty

    module All =
      State_builder.Hashtbl
        (Datatype.String.Hashtbl)
        (Datatype.Pair (Typ) (Datatype.Option (Datatype.Int)))
        (struct
          let name = "Jessie.Common.Type.Integral.All"
          let dependencies = [Framac.Ast.self]
          let size = 5
        end)

    let name ?bitsize ty =
      let name_it signed size_in_bytes =
        let nbits = bitsize |? 8 * size_in_bytes in
        if nbits <= 0 then
          Console.abort "Cannot translate an integral bit-field type `%a' of width %d <= 0 to Jessie enum type"
            Printer.pp_typ ty nbits;
        let name = (if signed then "" else "u") ^ "int" ^ (string_of_int nbits) in
        All.replace name (ty, Some nbits);
        name
      in
      let name_bool () =
        let name = "_bool" in
        All.replace name (ty, None);
        name
      in
      match unrollType ty with
      | TInt (IBool, _attr) -> name_bool ()
      | TInt (ik, _attr) ->
        name_it (isSigned ik) (IKind.size_in_bytes ik)
      | TEnum ({ ekind = IBool }, _) -> name_bool ()
      | TEnum ({ ekind = ik }, _) -> name_it (isSigned ik) (IKind.size_in_bytes ik)
      | _ -> Console.fatal "Type.Integral.name: non-integral type: %a" Printer.pp_typ ty

    let of_bitsize_u (s, u) = TInt (intKindForSize (s lsr 3) u, [])

    let add_by_name =
      let int_type_regexp =
        let u = "\\(u?\\)" in
        let int = "int" in
        let bits = "\\(8\\|16\\|32\\|64\\)" in
        Str.regexp @@ u ^ int ^ bits
      in
      fun name' ->
        let matches, group = Str.(string_match int_type_regexp name' 0, fun n -> matched_group n name') in
        if matches &&
           let bitsize = int_of_string (group 2)
           and unsigned = group 1 <> "" in
           let typ = of_bitsize_u (bitsize, unsigned) in
           name' = name ~bitsize typ
           (* Here the type is added to the table as side effect *)
        then ()
        else raise Not_found

    let iter_all = All.iter
    let fold_all = All.fold
  end
end

module Do =
struct

  let retaining_size_of_composite ci f =
    let original_size = Type.Composite.Ci.size ci in
    let result = f ci in
    Type.Composite.Ci.fix_size ?original_size ci;
    result

  let retaining_size_of_field fi f =
    let dimensions fi =
      let ci = fi.fcomp in
      let ty = TComp (ci, empty_size_cache (), []) in
      let off, nextoff =
        if ci.cstruct then
          let rec rest =
            function
            | { fcomp = { ckey }; fname } :: rest
              when ckey = ci.ckey && fname = fi.fname -> rest
            | _ :: rst -> rest rst
            | [] -> assert false (* The composite should necessarily contain its field *)
          in
          let rest = rest ci.cfields in
          let bits_offset fi = fst @@ bitsOffset ty @@ Field (fi, NoOffset) in
          bits_offset fi, match rest with fi :: _ -> bits_offset fi | [] -> bitsSizeOf ty - 8 * bytesAlignOf ty
        else
          0, snd @@ bitsOffset ty @@ Field (fi, NoOffset)
      in
      off, nextoff, bytesSizeOf ty
    in
    let original_dimensions = dimensions fi in
    let result = f fi in
    let dimensions = dimensions fi in
    if dimensions <> original_dimensions then begin
      let off, nextoff, _ = original_dimensions in
      fi.fbitfield <- Some (nextoff - off);
      fi.fattr <- addAttribute (Attr (Name.Attr.packed, [])) fi.fattr;
    end;
    result

  (* Delaying updates to the file until after the action function has
   * completed its work, to avoid visiting a newly created global or
   * initialization.
  *)

  type 'a attach =
    (<
      global : global -> unit;
      globaction : (unit -> unit) -> unit;
      ..
     > as 'a)

  type attaching_action = { perform : 'a. attach:'a attach -> file -> unit }

  let attaching_globs action file =
    let globals = ref [] in
    let globactions = ref [] in
    let attach_globaction = ref (fun action -> globactions := action :: !globactions) in
    let attach_global = ref (fun g -> globals := g :: !globals) in
    let perform_globactions () = List.iter (fun f -> f ()) !globactions in
    let detach_globals file =
        file.globals <- (List.rev !globals) @ file.globals;
        List.iter
          (function GVar (v, init, _) -> Globals.Vars.add v init | _ -> ()) !globals
    in
    action.perform
      ~attach:(object
        method global = !attach_global
        method globaction = !attach_globaction
      end)
      file;
    attach_globaction := (fun _ -> Console.fatal "attach#globaction: called on already dead object");
    attach_global := (fun _ -> Console.fatal "attach#global: called on already dead object");
    perform_globactions ();
    detach_globals file

  let on_x ~to_x_env ~of_x_env ?(wrap=Fn.id) f x =
    match f with
    | None -> x
    | Some f ->
      to_x_env x |>
      map_fst @@ wrap f |>
      of_x_env

  let on_term_offset =
    let on_term_offset = Ast.Term.(on_x ~to_x_env:offset_to_offset_env ~of_x_env:offset_of_offset_env) in
    fun ?pre ?post toff ->
    ChangeDoChildrenPost (on_term_offset pre toff, on_term_offset post)

  let on_term_lval  =
    let on_term_lval = Ast.Term.(on_x ~to_x_env:lval_to_lval_env ~of_x_env:lval_of_lval_env) in
    fun ?pre ?post tlv ->
    ChangeDoChildrenPost (on_term_lval pre tlv, on_term_lval post)

  let on_term =
    let on_term = Ast.Term.(on_x ~to_x_env:to_exp_env ~of_x_env:of_exp_env ~wrap:map_under_info) in
    fun ?pre ?post t ->
    ChangeDoChildrenPost (on_term pre t, on_term post)

end

module Visit =
struct

  type insert =
    {
      before : stmt list;
      after : stmt list
    }

  let prepend ({ before } as acc) stmt = { acc with before = stmt :: before }
  let append ({ after } as acc) stmt = { acc with after = stmt :: after }
  let insert { before = befores; after = afters } ~before ~after =
    { before = before :: befores; after = after :: afters }

  let prepending before = { before; after = [] }
  let appending after = { before = []; after }
  let inserting ~before ~after = { before; after }
  let inserting_nothing = { before = []; after = [] }
  let do_nothing x = x, inserting_nothing
  let of_action f x = f x, inserting_nothing

  module Local =
    struct
      type 'a visit_action =
        | SkipChildren of insert
        | DoChildren of insert
        | DoChildrenPost of ('a -> 'a * insert) * insert
        | JustCopy of insert
        | JustCopyPost of ('a -> 'a * insert) * insert
        | ChangeTo of 'a * insert
        | ChangeToPost of 'a * ('a -> 'a * insert) * insert
        | ChangeDoChildrenPost of 'a * ('a -> 'a * insert) * insert

      let to_visit_action =
        function[@warning "-42"]
        | Cil.SkipChildren -> SkipChildren inserting_nothing
        | DoChildren -> DoChildren inserting_nothing
        | DoChildrenPost f -> DoChildrenPost (of_action f, inserting_nothing)
        | JustCopy -> JustCopy inserting_nothing
        | JustCopyPost f -> JustCopyPost (of_action f, inserting_nothing)
        | ChangeTo x -> ChangeTo (x, inserting_nothing)
        | ChangeToPost (x, f) -> ChangeToPost (x, of_action f, inserting_nothing)
        | ChangeDoChildrenPost (x, f) -> ChangeDoChildrenPost (x, of_action f, inserting_nothing)
    end

  (* 'result parameter is added to the context type in order ro allow visitor method definitions like the following:
   * let f (type a) (type result) (type visit_action) : a -> (a, result, visit_action) context -> visit_action =
   *   fun a context ->
   *   let f : a -> result =
   *     fun a ->
   *     match context with
   *     | Local _ -> a, inserting_nothing
   *     | Global -> a
   *    in
   *    match context with
   *    | Local _ -> Local.ChangeToPost (a, f, inserting_nothing)
   *    | Global -> ChangeToPost (a, f)
   *)

  type ('a, 'result, 'visit_action) context =
    | Local : fundec -> ('a, 'a * insert, 'a Local.visit_action) context
    | Global : ('a, 'a, 'a visitAction) context

  open Local

  module Fundec =
    struct
      type 'a visit_action =
        | SkipChildren of insert
        | DoChildren of insert
        | DoChildrenPost of ('a -> 'a * insert) * insert
        | JustCopy of insert
        | JustCopyPost of ('a -> 'a * insert) * insert
        | ChangeTo of 'a
        | ChangeToPost of 'a * ('a -> 'a * insert)
        | ChangeDoChildrenPost of 'a * ('a -> 'a * insert)

      let to_visit_action =
        function[@warning "-42"]
        | Cil.SkipChildren -> SkipChildren inserting_nothing
        | DoChildren -> DoChildren inserting_nothing
        | DoChildrenPost f -> DoChildrenPost (of_action f, inserting_nothing)
        | JustCopy -> JustCopy inserting_nothing
        | JustCopyPost f -> JustCopyPost (of_action f, inserting_nothing)
        | ChangeTo x -> ChangeTo x
        | ChangeToPost (x, f) -> ChangeToPost (x, of_action f)
        | ChangeDoChildrenPost (x, f) -> ChangeDoChildrenPost (x, of_action f)
    end

  type ('a, 'r, 'v) visitor_method = 'a -> ('a, 'r, 'v) context -> 'v

  let to_visit_action
      (type a) (type result) (type visit_action) : a visitAction -> (a, result, visit_action) context -> visit_action =
    fun va ->
    function
    | Local _ -> Local.to_visit_action va
    | Global -> va

  class frama_c_inplace_inserting (self : #frama_c_visitor) =
    let do_children _ = to_visit_action Cil.DoChildren in
    let do_children_local _  (_ : fundec) = Local.DoChildren inserting_nothing in
    let do_children_global _ = Cil.DoChildren in
    object
      method set_current_kf = self#set_current_kf
      method set_current_func = self#set_current_func
      method current_kf = self#current_kf
      method current_func = self#current_func
      method push_stmt = self#push_stmt
      method pop_stmt = self#pop_stmt
      method current_stmt = self#current_stmt
      method current_kinstr = self#current_kinstr
      method get_filling_actions = self#get_filling_actions
      method fill_global_tables = self#fill_global_tables

      method videntified_term : 'a 'b. (identified_term, 'a, 'b) visitor_method = do_children
      method videntified_predicate : 'a 'b. (identified_predicate, 'a, 'b) visitor_method = do_children
      method vlogic_label : 'a 'b. (logic_label, 'a, 'b) visitor_method  = do_children

      method vfunc : fundec -> fundec Fundec.visit_action = fun _ -> Fundec.DoChildren (inserting_nothing)
      method vfile : file -> file visitAction = do_children_global
      method vglob_aux : global -> global list visitAction = do_children_global

      method vstmt_aux_inserting : stmt -> fundec -> stmt Local.visit_action = do_children_local

      method vblock : block -> fundec -> block Local.visit_action = do_children_local
      method vvrbl : 'a 'b. (varinfo, 'a, 'b) visitor_method = do_children
      method vvdec : 'a 'b. (varinfo, 'a, 'b) visitor_method = do_children
      method vexpr: 'a 'b. (exp, 'a, 'b) visitor_method = do_children
      method vlval : 'a 'b. (lval, 'a, 'b) visitor_method = do_children
      method voffs : 'a 'b. (offset, 'a, 'b) visitor_method  = do_children
      method vinitoffs : 'a 'b. (offset, 'a, 'b) visitor_method = do_children
      method vinst : instr -> fundec -> instr list Local.visit_action = do_children_local
      method vinit : 'a 'b. varinfo -> offset -> init -> (init, 'a, 'b) context -> 'b =
        fun _ _ _ -> to_visit_action Cil.DoChildren
      method vtype : 'a 'b. (typ, 'a, 'b) visitor_method = do_children
      method vattr : 'a 'b. attribute list -> (attribute list, 'a, 'b) context -> 'b  = do_children
      method vattrparam : 'a 'b. (attrparam, 'a, 'b) visitor_method = do_children

      method vlogic_type : 'a 'b. (logic_type, 'a, 'b) visitor_method = do_children
      method vterm : 'a 'b. (term, 'a, 'b) visitor_method = do_children
      method vterm_node : 'a 'b. (term_node, 'a, 'b) visitor_method = do_children
      method vterm_lval : 'a 'b. (term_lval, 'a, 'b) visitor_method = do_children
      method vterm_lhost : 'a 'b. (term_lhost, 'a, 'b) visitor_method = do_children
      method vterm_offset : 'a 'b. (term_offset, 'a, 'b) visitor_method = do_children
      method vlogic_info_decl : logic_info -> logic_info visitAction = do_children_global
      method vlogic_info_use : 'a 'b. (logic_info, 'a, 'b) visitor_method = do_children
      method vlogic_var_decl : 'a 'b. (logic_var, 'a, 'b) visitor_method = do_children
      method vlogic_var_use : 'a 'b. (logic_var, 'a, 'b) visitor_method = do_children
      method vquantifiers : 'a 'b. (quantifiers, 'a, 'b) visitor_method = do_children
      method vpredicate_node : 'a 'b. (predicate_node, 'a, 'b) visitor_method = do_children
      method vpredicate : 'a 'b. (predicate, 'a, 'b) visitor_method = do_children
      method vmodel_info : model_info -> model_info visitAction = do_children_global

      method vbehavior : 'a 'b. (funbehavior, 'a, 'b) visitor_method = do_children
      method vspec : 'a 'b. (funspec, 'a, 'b) visitor_method = do_children
      method vassigns : 'a 'b. (assigns, 'a, 'b) visitor_method = do_children
      method vloop_pragma : loop_pragma -> fundec -> loop_pragma Local.visit_action = do_children_local
      method vslice_pragma : 'a 'b. (slice_pragma, 'a, 'b) visitor_method = do_children
      method vjessie_pragma : jessie_pragma -> fundec -> jessie_pragma Local.visit_action = do_children_local
      method vimpact_pragma : 'a 'b. (impact_pragma, 'a, 'b) visitor_method = do_children
      method vdeps : 'a 'b. (deps, 'a, 'b) visitor_method = do_children
      method vfrom : 'a 'b. (from, 'a, 'b) visitor_method = do_children
      method vcode_annot : code_annotation -> fundec -> code_annotation Local.visit_action = do_children_local
      method vannotation : global_annotation -> global_annotation visitAction = do_children_global

      method behavior = self#behavior
      method project = self#project
      method frama_c_plain_copy = self#frama_c_plain_copy
      method plain_copy_visitor = self#plain_copy_visitor
      method queueInstr = self#queueInstr
      method reset_current_func = self#reset_current_func
      method reset_current_kf = self#reset_current_kf
      method unqueueInstr = self#unqueueInstr

      method vcompinfo : compinfo -> compinfo visitAction = do_children_global
      method venuminfo : enuminfo -> enuminfo visitAction = do_children_global
      method venumitem : enumitem -> enumitem visitAction = do_children_global
      method vfieldinfo : fieldinfo -> fieldinfo visitAction = do_children_global
      method vglob = self#vglob

      method vlogic_ctor_info_decl : logic_ctor_info -> logic_ctor_info visitAction = do_children_global
      method vlogic_ctor_info_use : 'a 'b. (logic_ctor_info, 'a, 'b) visitor_method = do_children
      method vlogic_type_def : logic_type_def -> logic_type_def visitAction = do_children_global
      method vlogic_type_info_decl : logic_type_info -> logic_type_info visitAction = do_children_global
      method vlogic_type_info_use : 'a 'b. (logic_type_info, 'a, 'b) visitor_method = do_children
      method vstmt = self#vstmt

      (*      method vbehavior_annot : *)

      method vallocates : 'a 'b. (identified_term list, 'a, 'b) visitor_method = do_children
      method vallocation : 'a 'b. (allocation, 'a, 'b) visitor_method = do_children
      method vfrees : 'a 'b. (identified_term list, 'a, 'b) visitor_method = do_children
    end

  module Inserting_visitor =
    struct
      type 'a inserting_visitor = { mk : 'b. (#frama_c_visitor as 'b) -> (#frama_c_inplace_inserting as 'a) }
    end

  include Inserting_visitor

  type 'a visitor_function = { visit: 'r 'v. ('a, 'r, 'v) visitor_method }

  class proxy_frama_c_visitor =
    let visitor = ref (new frama_c_inplace_inserting (new frama_c_inplace)) in
    fun inserting_visitor ->
    let insert, before, after =
      let pending_before = ref [] and pending_after = ref [] in
      (fun { before; after } ->
         pending_before := List.append before !pending_before;
         pending_after := List.append after !pending_after),
      (fun () -> let result = !pending_before in pending_before := []; result),
      fun () -> let result = !pending_after in pending_after := []; result
    in
    let post f = fun x -> let result, i = f x in insert i; result in
    let unwrap =
      function[@warning "-42"]
      | SkipChildren i -> insert i; Cil.SkipChildren
      | DoChildren i -> insert i;  DoChildren
      | DoChildrenPost (f, i) -> insert i; DoChildrenPost (post f)
      | JustCopy i -> insert i; JustCopy
      | JustCopyPost (f, i) -> insert i; JustCopyPost (post f)
      | ChangeTo (x, i) -> insert i; ChangeTo x
      | ChangeToPost (a, f, i) -> insert i; ChangeToPost (a, post f)
      | ChangeDoChildrenPost (a, f, i) -> insert i; ChangeDoChildrenPost (a, post f)
    in
    let cond { visit } x =
      match !visitor#current_func with
      | Some fundec -> unwrap (visit x @@ Local fundec)
      | None -> visit x Global
    in
    let local visit x =
      match !visitor#current_func with
      | Some fundec -> unwrap (visit x fundec)
      | None -> Console.fatal "unexpectedly visited global AST node as local"
    in
    let global visit =
      begin match !visitor#current_func with
      | Some fundec ->
        Console.debug "unexpectedly visited local AST node as global: %a" Printer.pp_varinfo fundec.svar;
      | None -> ()
      end;
      visit
    in
    let insert_pending_statements f =
      f.sbody.bstmts <- List.rev_append (before ()) f.sbody.bstmts;
      match after () with
      | [] -> ()
      | slist ->
        (* Insert pending statements before return statement *)
        let return_stmt = Kernel_function.find_return (Globals.Functions.get f.svar) in
        (* Remove labels from the single return statement. Leave them on the most
           * external block with cleanup code instead.
        *)
        let s = { return_stmt with labels = [] } in
        let block = mkBlock (List.rev_append (s :: slist) []) in
        return_stmt.skind <- Block block
    in
    object(self)
      inherit frama_c_inplace

      initializer
        visitor := (inserting_visitor.mk self :> frama_c_inplace_inserting)

      method! videntified_term = cond { visit = fun c -> !visitor#videntified_term c }
      method! videntified_predicate = cond { visit = fun c -> !visitor#videntified_predicate c }
      method! vlogic_label = cond { visit = fun c -> !visitor#vlogic_label c}

      (* Modify visitor on functions so that it prepends/postpends statements *)
      method! vfunc f =
        let post action x =
          let result = post action x in
          insert_pending_statements x;
          result
        in
        let open Fundec in
        let default_post = post (fun x -> x, inserting_nothing) in
        match[@warning "-42"] !visitor#vfunc f with
        | SkipChildren i -> insert i; Cil.ChangeToPost (f, default_post)
        | JustCopy i -> insert i; JustCopyPost default_post
        | JustCopyPost (action, i) -> insert i; JustCopyPost (post action)
        | ChangeTo f -> ChangeToPost (f, default_post)
        | ChangeToPost (f, action) -> ChangeToPost (f, post action)
        | DoChildren i -> insert i; DoChildrenPost default_post
        | DoChildrenPost (action, i) -> insert i; DoChildrenPost (post action)
        | ChangeDoChildrenPost (f, action) -> ChangeDoChildrenPost (f, post action)

      (* Inherit all other visitors *)

      (* Methods introduced by the Frama-C visitor *)
      method! vfile = !visitor#vfile
      method! vglob_aux = !visitor#vglob_aux
      method! vstmt_aux = local !visitor#vstmt_aux_inserting

      (* Methods from Cil visitor for coding constructs *)
      method! vblock = local !visitor#vblock
      method! vvrbl = cond { visit = fun x -> !visitor#vvrbl x }
      method! vvdec = cond { visit = fun x -> !visitor#vvdec x }
      method! vexpr = cond { visit = fun x -> !visitor#vexpr x }
      method! vlval = cond { visit = fun x -> !visitor#vlval x }
      method! voffs = cond { visit = fun x -> !visitor#voffs x }
      method! vinitoffs = cond { visit = fun x -> !visitor#vinitoffs x }
      method! vinst = local !visitor#vinst
      method! vinit vi off = cond { visit = fun x -> !visitor#vinit vi off x }
      method! vtype = cond { visit = fun x -> !visitor#vtype x }
      method! vattr a = cond { visit = fun x -> !visitor#vattr x } [a]
      method! vattrparam = cond { visit = fun x -> !visitor#vattrparam x }

      (* Methods from Cil visitor for logic constructs *)
      method! vlogic_type = cond { visit = fun x -> !visitor#vlogic_type x }
      method! vterm = cond { visit = fun x -> !visitor#vterm x }
      method! vterm_node = cond { visit = fun x -> !visitor#vterm_node x }
      method! vterm_lval = cond { visit = fun x -> !visitor#vterm_lval x }
      method! vterm_lhost = cond { visit = fun x -> !visitor#vterm_lhost x }
      method! vterm_offset = cond { visit = fun x -> !visitor#vterm_offset x }
      method! vlogic_info_decl = global !visitor#vlogic_info_decl
      method! vlogic_info_use = cond { visit = fun x -> !visitor#vlogic_info_use x }
      method! vlogic_var_decl = cond { visit = fun x -> !visitor#vlogic_var_decl x }
      method! vlogic_var_use = cond { visit = fun x -> !visitor#vlogic_var_use x }
      method! vquantifiers = cond { visit = fun x -> !visitor#vquantifiers x }
      method! vpredicate_node = cond { visit = fun x -> !visitor#vpredicate_node x }
      method! vpredicate = cond { visit = fun x -> !visitor#vpredicate x }
      method! vmodel_info = global !visitor#vmodel_info
      method! vbehavior = cond { visit = fun x -> !visitor#vbehavior x }
      method! vspec = cond { visit = fun x -> !visitor#vspec x }
      method! vassigns = cond { visit = fun x -> !visitor#vassigns x }
      method! vloop_pragma = local !visitor#vloop_pragma
      method! vslice_pragma = cond { visit = fun x -> !visitor#vslice_pragma x }
      method! vjessie_pragma = local !visitor#vjessie_pragma
      method! vdeps = cond { visit = fun x -> !visitor#vdeps x }
      method! vcode_annot = local !visitor#vcode_annot
      method! vannotation = global !visitor#vannotation

      method! vcompinfo = global !visitor#vcompinfo
      method! venuminfo = global !visitor#venuminfo
      method! venumitem = global !visitor#venumitem
      method! vfieldinfo = global !visitor#vfieldinfo
      method! vfrom = cond { visit = fun x -> !visitor#vfrom x }

      method! vimpact_pragma = cond { visit = fun x -> !visitor#vimpact_pragma x }
      method! vlogic_ctor_info_decl = global !visitor#vlogic_ctor_info_decl
      method! vlogic_ctor_info_use = cond { visit = fun x -> !visitor#vlogic_ctor_info_use x }
      method! vlogic_type_def = global !visitor#vlogic_type_def
      method! vlogic_type_info_decl = global !visitor#vlogic_type_info_decl
      method! vlogic_type_info_use = cond { visit = fun x -> !visitor#vlogic_type_info_use x }

      method! vallocates = cond { visit = fun x -> !visitor#vallocates x }
      method! vallocation = cond { visit = fun x -> !visitor#vallocation x }
      method! vfrees = cond { visit = fun x -> !visitor#vfrees x }
    end

  type 'a attaching_visitor = { mk : 'b. attach:'b Do.attach -> (#frama_c_visitor as 'a) }

  let attaching_globs visitor file =
    let perform ~attach = visitFramacFile @@ (visitor.mk attach :> frama_c_visitor) in
    Do.attaching_globs { Do.perform } file

  let inserting_statements visitor file =
    visitFramacFile (new proxy_frama_c_visitor visitor) file

  type 'a inserting_attaching_visitor =
    { mk : 'b 'c. attach:'b Do.attach -> (#frama_c_visitor as 'c) -> (#frama_c_inplace_inserting as 'a) }

  let inserting_statements_and_attaching_globs visitor file =
    let perform ~attach =
      visitFramacFile @@ new proxy_frama_c_visitor @@ { Inserting_visitor.mk = fun vis -> visitor.mk ~attach vis }
    in
    Do.attaching_globs { Do.perform } file

  type 'a signal =
    (<
      change : unit;
      ..
    > as 'a)

  type 'a fixpoint_visitor = { mk : 'b. signal:'b signal -> (#frama_c_visitor as 'a) }

  let until_convergence visitor file =
    let changed = ref false in
    let signal, prohibit, allow =
      let signal = fun () -> changed := true in
      let prohibited = fun () -> Console.fatal "signal#change: called on already dead object" in
      let signal_ref = ref signal in
      signal_ref, (fun () -> signal_ref := prohibited), fun () -> signal_ref := signal
    in
    let refresh () = changed := false in
    let visitor = (visitor.mk ~signal:(object method change = !signal () end) :> frama_c_visitor) in
    while (prohibit (); not !changed) do
      refresh ();
      allow ();
      visitFramacFile visitor file
    done
end

module Debug =
  struct
    class exp_typechecking_visitor =
      object
        inherit frama_c_inplace

        method! vexpr e =
          ignore (typeOf e);
          DoChildren
      end

    let check_exp_types file =
      if Config.debug_atleast 2 then begin
        visitFramacFile (new exp_typechecking_visitor) file;
        Jessie_options.debug ~level:2 "%a@." Printer.pp_file file
      end
end

(*****************************************************************************)
(* Trie data structure (by Jean-Christophe Filliatre)                        *)
(*****************************************************************************)

module Trie =
struct

  (* GPL-licensed OCaml trie implementation from https://www.lri.fr/~filliatr/ftp/ocaml/ds/trie.ml.html *)

  (*s A trie is a tree-like structure to implement dictionaries over
      keys which have list-like structures. The idea is that each node
      branches on an element of the list and stores the value associated
      to the path from the root, if any. Therefore, a trie can be
      defined as soon as a map over the elements of the list is
      given. *)

  module type Map =
  sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

  module type S =
  sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : 'a t -> key list -> 'a -> 'a t
    val find_exn : 'a t -> key list -> 'a
    val find_all : 'a t -> key list -> 'a list
    val find_all2 : 'a t -> key list -> (key list * 'a) list
    val remove : 'a t -> key list -> 'a t
    val remove_all : 'a t -> key list -> 'a t
    val mem : 'a t -> key list -> bool
    val mem_any : 'a t -> key list -> bool
    val iter : (key list -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key list -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key list -> 'a -> 'b -> 'b) -> 'b -> 'a t -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

  module Make (M : Map) =
  struct

    (*s Then a trie is just a tree-like structure, where a possible
        information is stored at the node (['a option]) and where the sons
        are given by a map from type [key] to sub-tries, so of type
        ['a t M.t]. The empty trie is just the empty map. *)

    type key = M.key

    type 'a t = Node of 'a option * 'a t M.t

    let empty = Node (None, M.empty)

    (*s To find a mapping in a trie is easy: when all the elements of the
        key have been read, we just inspect the optional info at the
        current node; otherwise, we descend in the appropriate sub-trie
        using [M.find]. *)

    let rec find_exn t l =
      match l, t with
      | [], Node (None, _)   -> raise Not_found
      | [], Node (Some v, _) -> v
      | x :: r, Node (_, m)    -> find_exn (M.find x m) r

    let rec mem t l =
      match l, t with
      | [], Node (None, _)   -> false
      | [], Node (Some _, _) -> true
      | x :: r, Node (_, m)   -> try mem (M.find x m) r with Not_found -> false

    (*s Insertion is more subtle. When the final node is reached, we just
        put the information ([Some v]). Otherwise, we have to insert the
        binding in the appropriate sub-trie [t']. But it may not exists,
        and in that case [t'] is bound to an empty trie. Then we get a new
        sub-trie [t''] by a recursive insertion and we modify the
        branching, so that it now points to [t''], with [M.add]. *)

    let add t l v =
      let rec ins =
        function
        | [], Node (_, m) -> Node (Some v, m)
        | x :: r, Node (v, m) ->
          let t = try M.find x m with Not_found -> empty in
          let t = ins (r, t) in
          Node (v, M.add x t m)
      in
      ins (l, t)

    (*s When removing a binding, we take care of not leaving bindings to empty
        sub-tries in the nodes. Therefore, we test wether the result [t'] of
        the recursive call is the empty trie [empty]: if so, we just remove
        the branching with [M.remove]; otherwise, we modify it with [M.add]. *)

    let rec remove t l =
      match l, t with
      | [], Node (_, m) -> Node (None, m)
      | x :: r, Node (v, m) ->
        try
          let t = remove (M.find x m) r in
          Node (v, if t = empty then M.remove x m else M.add x t m)
        with Not_found -> t

    (*s The iterators [map], [mapi], [iter] and [fold] are implemented in
        a straigthforward way using the corresponding iterators [M.map],
        [M.mapi], [M.iter] and [M.fold]. For the last three of them,
        we have to remember the path from the root, as an extra argument
        [revp]. Since elements are pushed in reverse order in [revp],
        we have to reverse it with [List.rev] when the actual binding
        has to be passed to function [f]. *)

    let rec map f =
      function
      | Node (None,m)   -> Node (None, M.map (map f) m)
      | Node (Some v,m) -> Node (Some (f v), M.map (map f) m)

    let mapi f t =
      let rec maprec revp =
        function
        | Node (None,m) ->
          Node (None, M.mapi (fun x -> maprec (x::revp)) m)
        | Node (Some v,m) ->
          Node (Some (f (List.rev revp) v), M.mapi (fun x -> maprec (x::revp)) m)
      in
      maprec [] t

    let iter f t =
      let rec traverse revp =
      function
      | Node (None,m) ->
        M.iter (fun x -> traverse (x::revp)) m
      | Node (Some v,m) ->
        f (List.rev revp) v; M.iter (fun x t -> traverse (x::revp) t) m
      in
      traverse [] t

    let fold f acc t =
      let rec traverse revp t acc =
        match t with
        | Node (None,m) ->
          M.fold (fun x -> traverse (x::revp)) m acc
        | Node (Some v,m) ->
          f (List.rev revp) v (M.fold (fun x -> traverse (x::revp)) m acc)
      in
      traverse [] t acc

    let compare cmp a b =
      let rec comp a b =
        match a,b with
        | Node (Some _, _), Node (None, _) -> 1
        | Node (None, _), Node (Some _, _) -> -1
        | Node (None, m1), Node (None, m2) ->
          M.compare comp m1 m2
        | Node (Some a, m1), Node (Some b, m2) ->
          let c = cmp a b in
          if c <> 0 then c else M.compare comp m1 m2
      in
      comp a b

    let equal eq a b =
      let rec comp a b =
        match a,b with
        | Node (None, m1), Node (None, m2) ->
          M.equal comp m1 m2
        | Node (Some a, m1), Node (Some b, m2) ->
          eq a b && M.equal comp m1 m2
        | _ ->
          false
      in
      comp a b

    (* The base case is rather stupid, but constructable *)
    let is_empty =
      function
      | Node (None, m1) -> M.is_empty m1
      | _ -> false

    (*s The following functions operate on all the elements that have the keys
        strting with the same specified prefix. *)

    let find_all2 t l =
      let rec find_all2 acc t l =
        match l, t with
        | [], _               -> fold (fun l v acc -> (l, v) :: acc) acc t
        | x :: r, Node (_, m) -> try find_all2 acc (M.find x m) r with Not_found -> []
      in
      find_all2 [] t l

    let find_all t l = List.map snd (find_all2 t l)

    let rec remove_all t l =
      match l, t with
      | [], _             -> empty
      | x :: r, Node (v, m) ->
        try
          let t = remove_all (M.find x m) r in
          Node (v, if t = empty then M.remove x m else M.add x t m)
        with Not_found -> t

    let rec mem_any t l =
      match l, t with
      | [], _               -> is_empty t
      | x :: r, Node (_, m)   -> try mem_any (M.find x m) r with Not_found -> false

  end
end

module StringTrie = Trie.Make (Map.Make (Char))
module Int64Trie = Trie.Make (Map.Make (Int64))

(*
Local Variables:
compile-command: "LC_ALL=C make -C .. -j byte"
End:
*)
