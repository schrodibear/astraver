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
      [Emitter.Funspec; Emitter.Code_annot ]
      ~correctness:[Jessie_options.Behavior.parameter; Jessie_options.Infer_annot.parameter]
      ~tuning:[]
end

exception Unsupported of string

module Console =
struct
  let fatal fmt = Jessie_options.fatal ~current:true fmt
  let unsupported fmt =
    Jessie_options.with_failure
      (fun evt ->
         raise (Unsupported evt.Log.evt_message))
      ~current:true
      fmt
  let warning fmt = Jessie_options.warning ~current:true fmt
  let general_warning fmt = Jessie_options.warning ~current:false fmt
  let warn_once =
    let known_warns = Hashtbl.create 7 in
    fun s ->
      if not (Hashtbl.mem known_warns s) then begin
        Hashtbl.add known_warns s ();
        general_warning "%s" s
      end
  let debug fmt = Jessie_options.debug fmt
end

module List =
struct
  include List

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
      || String.contains "123456789" c
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

    let fdup2 f g x = f x, g x
    let map1 f (a, b) = f a, b
    let map2 f (a, b) = a, f b
    let map f (a, b) = f a, f b
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

let fdup2 = Pair.fdup2
let map_fst = Pair.map1
let map_snd = Pair.map2
let map_pair = Pair.map
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
end

let (|?) xo default = Option.value ~default xo

module Location =
struct
  include Location
  let is_unknown loc = (fst loc).Lexing.pos_lnum = 0
end

module Config =
struct
  include Jessie_options
  let flatten_multi_dim_arrays = false
end

module Framac =
struct
  module Ast = Ast
  module Type = Type
  module Vi = Varinfo
end

(* Redefine statement constructor of CIL to create them with valid sid *)
let mkStmt = mkStmt ~valid_sid:true

module Name =
struct
  module Of =
    struct
      module Attr =
      struct
        let embedded = "embedded_from"
        let noembed = "noembed"
        let padding = "padding"
        let wrapper = "wrapper"
        let arraylen = "arraylen"
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
        let string_declspec = "valid_string"
      end

      module Function =
      struct
        let assert_ = "assert"
        let free = "free"
        let kfree = "kfree"
        let malloc = "malloc"
        let kmalloc = "kmalloc"
        let kzalloc = "kzalloc"
        let calloc = "calloc"
        let realloc = "realloc"
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
    end

  let predefined_name =
    Of.Function.[ (* coding functions *)
      assert_;
      malloc;
      kmalloc;
      kzalloc;
      calloc;
      realloc;
      free;
      kfree;
      Of.Logic_function.nondet_int
    ]

  let is_predefined s = List.mem s predefined_name

  let unique_generator is_exception =
    let unique_names = Hashtbl.create 127 in
    let rec aux ?(force=false) s =
      if not force && is_exception s then s else
        try
          let s = if s = "" then "unnamed" else s in
          let count = Hashtbl.find unique_names s in
          let s = s ^ "_" ^ (string_of_int !count) in
          if Hashtbl.mem unique_names s then
            aux s
          else
            (Hashtbl.add unique_names s (ref 0);
             incr count; s)
        with Not_found ->
          Hashtbl.add unique_names s (ref 0); s
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

  module Named =
  struct
    type 'a t = 'a named

    let mk ?(name=[]) ~loc content =
      {
        name;
        loc;
        content
      }
  end

  module Exp =
  struct
    type t = exp

    let const ?(loc=Location.unknown) n =
      Ast_info.constant_expr ~loc n

    let dummy_info e =
      match e.enode with
      | Info _ -> e
      | _ ->
        let einfo = { exp_type = Ctype voidType; exp_name = [] } in
        (* In many cases, the correct type may not be available, as
         * the expression may result from a conversion from a term or a tset.
         * Calling [typeOf] on such an expression may raise an error.
         * Therefore, put here a dummy type until tsets correctly typed.
         *)
        new_exp ~loc:e.eloc @@ Info (e, einfo)
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

      open Name.Of.Function
      let is_assert v = isFunctionType v.vtype && v.vname = assert_
      let is_free v = isFunctionType v.vtype && v.vname = free
      let is_kfree v = isFunctionType v.vtype && v.vname = kfree
      let is_malloc v = isFunctionType v.vtype && v.vname = malloc
      let is_kmalloc v = isFunctionType v.vtype && v.vname = kmalloc
      let is_kzalloc v = isFunctionType v.vtype && v.vname = kzalloc
      let is_calloc v = isFunctionType v.vtype && v.vname = calloc
      let is_realloc v = isFunctionType v.vtype && v.vname = realloc

      let malloc ?(kernel=false) () =
        let fname, params =
          let size = "size", uintType, [] in
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
        with Not_found ->
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
              (TCastE(Cil.charPtrType,Logic_const.tresult Cil.charPtrType)) typ
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
      | Ltype _ | Lvar _ | Larrow _ -> invalid_arg "Ast.Term.typ_of_logic_c_type"

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
          let ty = match t.term_type with Ctype ty -> ty | _ -> voidType in
          let v = makePseudoVar ty in
          let env = { env with terms = Varinfo.Map.add v t env.terms } in
          Lval (Var v, NoOffset), env

        let add_var env v =
          let ty = match v.lv_type with Ctype ty -> ty | _ -> assert false in
          let pv = makePseudoVar ty in
          let env = { env with vars = Varinfo.Map.add pv v env.vars } in
          Var pv, env

        let add_lhost env lhost =
          let v = makePseudoVar voidType in
          let env = { env with term_lhosts = Varinfo.Map.add v lhost env.term_lhosts } in
          Var v, env

        let add_result env ty =
          let pv = makePseudoVar ty in
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
        | TUnOp (unop,t') ->
          let e, env = to_exp_env t' in
          UnOp (unop, e, typ_of_logic_c_type t.term_type), env
        | TBinOp(binop,t1,t2) ->
          let e1, env1 = to_exp_env t1 in
          let e2, env2 = to_exp_env t2 in
          let env = Env.merge env1 env2 in
          BinOp (binop, e1, e2, typ_of_logic_c_type t.term_type), env
        | TSizeOfStr string -> SizeOfStr string, Env.empty
        | TLogic_coerce (Linteger, t) ->
          let e, env = to_exp_env t in
          CastE (TInt (IInt, [Attr ("integer", [])]), e), env
        | TLogic_coerce (Lreal, t) ->
          let e, env = to_exp_env t in
          CastE (TFloat (FFloat, [Attr ("real",[])]), e), env
        | TCastE (ty, t') ->
          let e, env = to_exp_env t' in CastE (ty, e), env
        | TAlignOf ty -> AlignOf ty, Env.empty
        | TSizeOf ty -> SizeOf ty, Env.empty
        | TConst c ->
          (try Const (const_of_lconst c), Env.empty with Exit -> Env.add_term Env.empty t)
        | Tapp _ | TDataCons _ | Tif _ | Tat _ | Tbase_addr _
        | Toffset _ | Toffset_max _ | Toffset_min _
        | Tblock_length _ | Tnull | TCoerce _ | TCoerceE _ | TUpdate _
        | Tlambda _ | Ttypeof _ | Ttype _ | Tcomprehension _
        | Tunion _ | Tinter _ | Tempty_set | Trange _ | Tlet _
        | TLogic_coerce _ ->
          Env.add_term Env.empty t
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
          | CastE (TInt (IInt, [Attr ("integer", [])]), e) ->
            TLogic_coerce (Linteger, of_exp_env' (e, env))
          | CastE (TFloat (FFloat, [Attr ("real", [])]), e) ->
            TLogic_coerce (Lreal, of_exp_env' (e, env))
          | CastE (ty, e) -> TCastE (ty, of_exp_env' (e, env))
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
        | CastE (ty, e) -> TCastE (ty, of_exp e)
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

    let rec of_exp_exn e =
      let pnode =
        match (stripInfo e).enode with
        | Info _ -> Console.fatal "Ast.Predicate.of_exp_exn: Info is unsupported: %a" Printer.pp_exp e
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
      { name = []; loc = e.eloc; content = pnode }
  end

  module Code_annot =
  struct
    type t = (term, predicate named, identified_predicate, identified_term) code_annot

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
              BinOp (Mult, idx1, Exp.const siz, intType)
          in
          (* Keep info at top-level for visitors on terms that where
           * translated to expressions. Those expect these info when
           * translating back to term.
           *)
          let addidx =
            map_under_info
              (fun e ->
                 new_exp ~loc:e.eloc @@ BinOp (PlusA, mulidx, idx, intType))
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
                   BinOp (Mult, idx1, Exp.const siz, intType))
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

  (* Type for ghost variables until integer is a valid type for ghosts. *)
  let almost_integer_type = TInt (ILongLong, [])
  let struct_type_for_void = voidType

  module Logic_c_type =
  struct

    let rec map_default ~default f =
      function
      | Ctype typ -> f typ
      | Ltype ({ lt_name = "set" }, [t]) -> map_default ~default f t
      | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ -> default

    let rec map f =
      function
      | Ctype typ -> f typ
      | Ltype ({ lt_name = "set" }, [t]) -> map f t
      | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ as ty ->
        Console.fatal "map_logic_c_type_exn: unexpected non-C type: %a" Printer.pp_logic_type ty
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
      let attr = addAttribute (Attr (Name.Of.Attr.arraylen, [siz])) attr in
      (* Avoid creating an array for single pointed elements that do not
       * originate in a C array, to avoid having to access to the first
       * element everywhere.  *)
      TPtr (elemty, attr)

    let array (elemty, size, attr) =
      (* Check the array size is of a correct form *)
      ignore (lenOfArray64 (Some size));
      let siz = expToAttrParam size in
      let attr = addAttribute (Attr (Name.Of.Attr.arraylen, [siz])) attr in
      (* Make the underlying type an array so that indexing it is still valid C. *)
      TPtr (TArray (elemty, Some size, empty_size_cache (), []), attr)

    let size ty =
      match findAttribute Name.Of.Attr.arraylen (typeAttrs ty) with
      | [AInt i] -> Integer.to_int64 i
      | _ -> Console.fatal "Type.Ref.size: non-reference type: %a" Printer.pp_typ ty

    let is_ref ty =
      isPointerType ty && hasAttribute Name.Of.Attr.arraylen (typeAttrs ty)

    let is_array_ref ty =
      is_ref ty && isArrayType (Cil.unrollType (direct_pointed_type ty))

    let of_array_exn ty =
      let rec reftype ty =
        if isArrayType ty then
          let elty = reftype (direct_element_type ty) in
          let size = Ast.Exp.const (direct_array_size ty) in
          array (elty, size, [])
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

      (* Wrappers on [mkCompInfo] that update size/offset of fields *)

        let empty stname =
          mkCompInfo true stname (fun _ -> []) []

        let singleton ?(padding=0) stname finame fitype =
          let compinfo =
            mkCompInfo true stname
              (fun _ -> [finame, fitype, None, [], CurrentLoc.get ()]) []
          in
          let fi = unique_field_exn @@ TComp (compinfo, empty_size_cache (), []) in
          fi.fsize_in_bits <- Some (bitsSizeOf fitype);
          fi.foffset_in_bits <- Some 0;
          fi.fpadding_in_bits <- Some padding;
          compinfo
      end

      let size ci =
        if ci.cdefined then Some (bitsSizeOf @@ TComp (ci, empty_size_cache (), []))
        else  None

      let padding_field =
        let padding_type = intType in
        fun ?fsize_in_bits ci ->
          { fcomp = ci;
            forig_name = "";
            fname = Name.unique "padding";
            ftype = padding_type;
            fbitfield = fsize_in_bits;
            fattr = [Attr ("const", []); Attr (Name.Of.Attr.padding, [])];
            floc = Location.unknown;
            faddrof = false;
            fsize_in_bits;
            foffset_in_bits = None;
            fpadding_in_bits = None }

      let fix_size ?original_size ci =
        let current_size = size ci in
        match original_size, current_size with
        | Some original_size, Some current_size ->
          List.iter (fun fi -> fi.foffset_in_bits <- None) ci.cfields;
          if current_size < original_size then
              ci.cfields <- ci.cfields @ [padding_field ~fsize_in_bits:(original_size - current_size) ci]
          else if current_size > original_size then
            let remaining_size_fix =
              List.fold_left
                (fun size_fix fi ->
                   if size_fix > 0 &&
                      not (hasAttribute Name.Of.Attr.embedded fi.fattr) &&
                      hasAttribute Name.Of.Attr.padding fi.fattr
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
        | _ -> ()

      let proper_fields ci = List.filter (fun fi -> not @@ hasAttribute Name.Of.Attr.padding fi.fattr) ci.cfields
    end
  end

  let promote_argument_type arg_type =
    match unrollType arg_type with
    | TVoid _ -> TVoid []
    | TInt (k, _) when rank k <= rank IInt -> TInt (IInt, [])
    | TInt (k, _) -> TInt (k, [])
    | TFloat (FFloat, _) -> TFloat (FDouble, [])
    | TFloat (k, _) -> TFloat (k, [])
    | TPtr (t, _) | TArray (t, _, _, _) -> TPtr (t, [])
    | TFun _ as t -> TPtr (t, [])
    | TComp (ci, _, _) -> TComp (ci, empty_size_cache (), [])
    | TEnum (ei, _) -> TEnum (ei, [])
    | TBuiltin_va_list _ ->
      Console.fatal ~current:true "promote_argument_type: variadic arguments"
    | TNamed _ -> assert false (* unrollType *)

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

    module IKind =
    struct
      type t = ikind

      let size_in_bytes =
        function
        | IBool -> assert false
        | IChar | ISChar | IUChar -> 1 (* Cil assumes char is one byte *)
        | IInt | IUInt -> theMachine.theMachine.sizeof_int
        | IShort | IUShort -> theMachine.theMachine.sizeof_short
        | ILong | IULong -> theMachine.theMachine.sizeof_long
        | ILongLong | IULongLong -> theMachine.theMachine.sizeof_longlong
    end

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

  let prepending before = { before; after = [] }
  let appending after = { before = []; after }
  let inserting ~before ~after = { before; after }
  let inserting_nothing = { before = []; after = [] }

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
    end

  (* 'result parameter is added to the context type in order ro allow visitor method definitions like the following:
   * let f (type a) (type result) (type visit_action) : (a, result, visit_action) context -> a -> visit_action =
   * fun context a ->
   *   let f : a -> result =
   *     fun a ->
   *     match context with
   *     | Local -> a, inserting_nothing
   *     | Global -> a
   *   in
   *   match context with
   *   | Local -> ChangeToPost (a, f, inserting_nothing)
   *   | Global -> ChangeToPost (a, f)
   *)

  type ('a, 'result, 'visit_action) context =
    | Local : ('a, ('a * insert) as 'result, 'a Local.visit_action) context
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
    end

  let wrap
      (type a)
      (type result)
      (type visit_action) :
      (a, result, visit_action) context -> a visitAction -> visit_action =
    function
    | Local ->
      let wrap = fun f x -> f x, inserting_nothing in
      (function[@warning "-42"]
        | SkipChildren -> SkipChildren (inserting_nothing)
        | DoChildren -> DoChildren (inserting_nothing)
        | DoChildrenPost f -> DoChildrenPost (wrap f, inserting_nothing)
        | JustCopy -> JustCopy (inserting_nothing)
        | JustCopyPost f -> JustCopyPost (wrap f, inserting_nothing)
        | ChangeTo x -> ChangeTo (x, inserting_nothing)
        | ChangeToPost (x, f) -> ChangeToPost (x, wrap f, inserting_nothing)
        | ChangeDoChildrenPost (x, f) -> ChangeDoChildrenPost (x, wrap f, inserting_nothing))
    | Global -> Fn.id


  type ('a, 'r, 'v) visitor_method = ('a, 'r, 'v) context -> 'a -> 'v

  class frama_c_inplace_inserting =
    let do_children = fun context _ -> wrap context Cil.DoChildren in
    let do_children_local = fun _ -> Local.DoChildren inserting_nothing in
    object
      val super = new frama_c_inplace

      method set_current_kf = super#set_current_kf
      method set_current_func = super#set_current_func
      method current_kf = super#current_kf
      method current_func = super#current_func
      method push_stmt = super#push_stmt
      method pop_stmt = super#pop_stmt
      method current_stmt = super#current_stmt
      method current_kinstr = super#current_kinstr
      method get_filling_actions = super#get_filling_actions
      method fill_global_tables = super#fill_global_tables

      method videntified_term : 'a 'b. (identified_term, 'a, 'b) visitor_method = do_children
      method videntified_predicate : 'a 'b. (identified_predicate, 'a, 'b) visitor_method = do_children
      method vlogic_label : 'a 'b. (logic_label, 'a, 'b) visitor_method  = do_children

      method vfunc : fundec -> fundec Fundec.visit_action = fun _ -> Fundec.DoChildren (inserting_nothing)
      method vfile = super#vfile
      method vglob_aux = super#vglob_aux

      method vstmt_aux : stmt -> stmt Local.visit_action = do_children_local

      method vblock : block -> block Local.visit_action = do_children_local
      method vvrbl : 'a 'b. (varinfo, 'a, 'b) visitor_method = do_children
      method vvdec : 'a 'b. (varinfo, 'a, 'b) visitor_method = do_children
      method vexpr: 'a 'b. (exp, 'a, 'b) visitor_method = do_children
      method vlval : 'a 'b. (lval, 'a, 'b) visitor_method = do_children
      method voffs : 'a 'b. (offset, 'a, 'b) visitor_method  = do_children
      method vinitoffs : 'a 'b. (offset, 'a, 'b) visitor_method = do_children
      method vinst : instr -> instr list Local.visit_action = do_children_local
      method vinit : 'a 'b. (init, 'a, 'b) context -> varinfo -> offset -> init -> 'b =
        fun context _ _ _ -> wrap context Cil.DoChildren
      method vtype : 'a 'b. (typ, 'a, 'b) visitor_method = do_children
      method vattr : 'a 'b. (attribute list, 'a, 'b) context -> attribute list -> 'b  = do_children
      method vattrparam : 'a 'b. (attrparam, 'a, 'b) visitor_method = do_children

      method vlogic_type : 'a 'b. (logic_type, 'a, 'b) visitor_method = do_children
      method vterm : 'a 'b. (term, 'a, 'b) visitor_method = do_children
      method vterm_node : 'a 'b. (term_node, 'a, 'b) visitor_method = do_children
      method vterm_lval : 'a 'b. (term_lval, 'a, 'b) visitor_method = do_children
      method vterm_lhost : 'a 'b. (term_lhost, 'a, 'b) visitor_method = do_children
      method vterm_offset : 'a 'b. (term_offset, 'a, 'b) visitor_method = do_children
      method vlogic_info_decl = super#vlogic_info_decl
      method vlogic_info_use : 'a 'b. (logic_info, 'a, 'b) visitor_method = do_children
      method vlogic_var_decl : 'a 'b. (logic_var, 'a, 'b) visitor_method = do_children
      method vlogic_var_use : 'a 'b. (logic_var, 'a, 'b) visitor_method = do_children
      method vquantifiers : 'a 'b. (quantifiers, 'a, 'b) visitor_method = do_children
      method vpredicate : 'a 'b. (predicate, 'a, 'b) visitor_method = do_children
      method vpredicate_named : 'a 'b. (predicate named, 'a, 'b) visitor_method = do_children
      method vmodel_info = super#vmodel_info

      method vbehavior : 'a 'b. (funbehavior, 'a, 'b) visitor_method = do_children
      method vspec : 'a 'b. (funspec, 'a, 'b) visitor_method = do_children
      method vassigns : 'a 'b. (identified_term assigns, 'a, 'b) visitor_method = do_children
      method vloop_pragma : term loop_pragma -> term loop_pragma Local.visit_action = do_children_local
      method vslice_pragma : 'a 'b. (term slice_pragma, 'a, 'b) visitor_method = do_children
      method vjessie_pragma : term jessie_pragma -> term jessie_pragma Local.visit_action = do_children_local
      method vimpact_pragma : 'a 'b. (term impact_pragma, 'a, 'b) visitor_method = do_children
      method vdeps : 'a 'b. (identified_term deps, 'a, 'b) visitor_method = do_children
      method vfrom : 'a 'b. (identified_term from, 'a, 'b) visitor_method = do_children
      method vcode_annot : code_annotation -> code_annotation Local.visit_action = do_children_local
      method vannotation = super#vannotation

      method behavior = super#behavior
      method project = super#project
      method frama_c_plain_copy = super#frama_c_plain_copy
      method plain_copy_visitor = super#plain_copy_visitor
      method queueInstr = super#queueInstr
      method reset_current_func = super#reset_current_func
      method reset_current_kf = super#reset_current_kf
      method unqueueInstr = super#unqueueInstr

      method vcompinfo = super#vcompinfo
      method venuminfo = super#venuminfo
      method venumitem = super#venumitem
      method vfieldinfo = super#vfieldinfo
      method vglob = super#vglob

      method vlogic_ctor_info_decl = super#vlogic_ctor_info_decl
      method vlogic_ctor_info_use : 'a 'b. (logic_ctor_info, 'a, 'b) visitor_method = do_children
      method vlogic_type_def = super#vlogic_type_def
      method vlogic_type_info_decl = super#vlogic_type_info_decl
      method vlogic_type_info_use : 'a 'b. (logic_type_info, 'a, 'b) visitor_method = do_children
      method vstmt : stmt -> stmt Local.visit_action = do_children_local

      method vallocates : 'a 'b. (identified_term list, 'a, 'b) visitor_method = do_children
      method vallocation : 'a 'b. (identified_term allocation, 'a, 'b) visitor_method = do_children
      method vfrees : 'a 'b. (identified_term list, 'a, 'b) visitor_method = do_children
    end

  class proxy_frama_c_visitor (visitor : #frama_c_inplace_inserting) : frama_c_visitor =
    let insert, before, after =
      let pending_before = ref [] and pending_after = ref [] in
      (fun { before; after } ->
         pending_before := List.append before !pending_before;
         pending_after := List.append after !pending_after),
      (fun () -> let result = !pending_before in pending_before := []; result),
      fun () -> let result = !pending_after in pending_after := []; result
    in
    let post f = fun x -> let result, i = f x in insert i; result in
    let cond : 'a 'b. ('a -> 'b Local.visit_action) -> ('a -> 'b visitAction) -> 'a -> 'b visitAction =
      fun a b x ->
      let unwrap =
        function[@warning "-42"]
        | SkipChildren i -> insert i; Cil.SkipChildren
        | DoChildren i -> insert i;  DoChildren
        | DoChildrenPost (f, i) -> insert i; DoChildrenPost (post f)
        | JustCopy i -> insert i; JustCopy
        | JustCopyPost (f, i) -> insert i; JustCopyPost (post f)
        | ChangeTo (x, i) -> insert i; ChangeTo x
        | ChangeToPost (a, f, i) -> insert i; Cil.ChangeToPost (a, post f)
        | ChangeDoChildrenPost (a, f, i) -> insert i; Cil.ChangeDoChildrenPost (a, post f)
      in
      if has_some visitor#current_func then
        unwrap (a x)
      else
        b x
    in
    let always_local : 'a 'b.  'a -> 'b visitAction =
      fun _ -> Console.fatal "unexpectedly visited global AST node as local"
    in
    let always_global : 'a 'b. 'a -> 'b visit_action =
      fun _ -> Console.fatal "unexpectedly visited local AST node as global"
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
    object
      (* [VP 2011-08-24]
       *  Do not inherit from Visitor.frama_c_visitor: all methods
       *  that are not overloaded have to come from visitor. Otherwise, proxy will
       *  fail to delegate some of its actions.
       *)

      method set_current_kf = visitor#set_current_kf
      method set_current_func = visitor#set_current_func
      method current_kf = visitor#current_kf
      method current_func = visitor#current_func
      method push_stmt = visitor#push_stmt
      method pop_stmt = visitor#pop_stmt
      method current_stmt = visitor#current_stmt
      method current_kinstr = visitor#current_kinstr
      method get_filling_actions = visitor#get_filling_actions
      method fill_global_tables = visitor#fill_global_tables

      method videntified_term = cond (visitor#videntified_term Local) (visitor#videntified_term Global)
      method videntified_predicate = cond (visitor#videntified_predicate Local) (visitor#videntified_predicate Global)
      method vlogic_label = cond (visitor#vlogic_label Local) (visitor#vlogic_label Global)

      (* Modify visitor on functions so that it prepends/postpends statements *)
      method vfunc f =
        let post action x =
          let result = post action x in
          insert_pending_statements x;
          result
        in
        let open Fundec in
        let default_post = post (fun x -> x, inserting_nothing) in
        match[@warning "-42"] visitor#vfunc f with
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
      method vfile = visitor#vfile
      method vglob_aux = visitor#vglob_aux
      method vstmt_aux = cond visitor#vstmt_aux always_local

      (* Methods from Cil visitor for coding constructs *)
      method vblock = cond visitor#vblock always_local
      method vvrbl = cond (visitor#vvrbl Local) (visitor#vvrbl Global)
      method vvdec = cond (visitor#vvdec Local) (visitor#vvdec Global)
      method vexpr = cond (visitor#vexpr Local) (visitor#vexpr Global)
      method vlval = cond (visitor#vlval Local) (visitor#vlval Global)
      method voffs = cond (visitor#voffs Local) (visitor#voffs Global)
      method vinitoffs = cond (visitor#vinitoffs Local) (visitor#vinitoffs Global)
      method vinst = cond visitor#vinst always_local
      method vinit vi off =
        cond (visitor#vinit Local vi off) (visitor#vinit Global vi off)
      method vtype = cond (visitor#vtype Local) (visitor#vtype Global)
      method vattr a = cond (visitor#vattr Local) (visitor#vattr Global) [a]
      method vattrparam = cond (visitor#vattrparam Local) (visitor#vattrparam Global)

      (* Methods from Cil visitor for logic constructs *)
      method vlogic_type = cond (visitor#vlogic_type Local) (visitor#vlogic_type Global)
      method vterm = cond (visitor#vterm Local) (visitor#vterm Global)
      method vterm_node = cond (visitor#vterm_node Local) (visitor#vterm_node Global)
      method vterm_lval = cond (visitor#vterm_lval Local) (visitor#vterm_lval Global)
      method vterm_lhost = cond (visitor#vterm_lhost Local) (visitor#vterm_lhost Global)
      method vterm_offset = cond (visitor#vterm_offset Local) (visitor#vterm_offset Global)
      method vlogic_info_decl = cond always_global visitor#vlogic_info_decl
      method vlogic_info_use = cond (visitor#vlogic_info_use Local) (visitor#vlogic_info_use Global)
      method vlogic_var_decl = cond (visitor#vlogic_var_decl Local) (visitor#vlogic_var_decl Global)
      method vlogic_var_use = cond (visitor#vlogic_var_use Local) (visitor#vlogic_var_use Global)
      method vquantifiers = cond (visitor#vquantifiers Local) (visitor#vquantifiers Global)
      method vpredicate = cond (visitor#vpredicate Local) (visitor#vpredicate Global)
      method vpredicate_named = cond (visitor#vpredicate_named Local) (visitor#vpredicate_named Global)
      method vmodel_info = cond always_global visitor#vmodel_info
      method vbehavior = cond always_global (visitor#vbehavior Global)
      method vspec = cond (visitor#vspec Local) (visitor#vspec Global)
      method vassigns = cond (visitor#vassigns Local) (visitor#vassigns Global)
      method vloop_pragma = cond visitor#vloop_pragma always_local
      method vslice_pragma = cond (visitor#vslice_pragma Local) (visitor#vslice_pragma Global)
      method vjessie_pragma = cond visitor#vjessie_pragma always_local
      method vdeps = cond (visitor#vdeps Local) (visitor#vdeps Global)
      method vcode_annot = cond visitor#vcode_annot always_local
      method vannotation = cond always_global visitor#vannotation

      method behavior = visitor#behavior
      method project = visitor#project
      method frama_c_plain_copy = visitor#frama_c_plain_copy
      method plain_copy_visitor = visitor#plain_copy_visitor
      method queueInstr = visitor#queueInstr
      method reset_current_func = visitor#reset_current_func
      method reset_current_kf = visitor#reset_current_kf
      method unqueueInstr = visitor#unqueueInstr
      method vcompinfo = cond always_global visitor#vcompinfo
      method venuminfo = cond always_global visitor#venuminfo
      method venumitem = cond always_global visitor#venumitem
      method vfieldinfo = cond always_global visitor#vfieldinfo
      method vfrom = cond (visitor#vfrom Local) (visitor#vfrom Global)
      method vglob = visitor#vglob
      method vimpact_pragma = cond (visitor#vimpact_pragma Local) (visitor#vimpact_pragma Global)
      method vlogic_ctor_info_decl = cond always_global visitor#vlogic_ctor_info_decl
      method vlogic_ctor_info_use = cond (visitor#vlogic_ctor_info_use Local) (visitor#vlogic_ctor_info_use Global)
      method vlogic_type_def = cond always_global visitor#vlogic_type_def
      method vlogic_type_info_decl = cond always_global visitor#vlogic_type_info_decl
      method vlogic_type_info_use = cond (visitor#vlogic_type_info_use Local) (visitor#vlogic_type_info_use Global)
      method vstmt = cond visitor#vstmt always_local

      method vallocates = cond (visitor#vallocates Local) (visitor#vallocates Global)
      method vallocation = cond (visitor#vallocation Local) (visitor#vallocation Global)
      method vfrees = cond (visitor#vfrees Local) (visitor#vfrees Global)
    end

  type attaching_visitor = { mk : 'a. attach:'a Do.attach -> frama_c_visitor }

  let attaching_globs visitor file =
    let perform ~attach = visitFramacFile @@ visitor.mk attach in
    Do.attaching_globs { Do.perform } file

  let inserting_statements visitor file =
    visitFramacFile (new proxy_frama_c_visitor visitor) file

  type 'a signal =
    (<
      change : unit;
      ..
    > as 'a)

  type fixpoint_visitor = { mk : 'a. signal:'a signal -> frama_c_visitor }

  let until_convergence visitor file =
    let changed = ref false in
    let signal, prohibit, allow =
      let signal = fun () -> changed := true in
      let prohibited = fun () -> Console.fatal "signal#change: called on already dead object" in
      let signal_ref = ref signal in
      signal_ref, (fun () -> signal_ref := prohibited), fun () -> signal_ref := signal
    in
    let refresh () = changed := false in
    let visitor = visitor.mk ~signal:(object method change = !signal () end) in
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
