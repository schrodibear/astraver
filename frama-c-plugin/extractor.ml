(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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

open Cil_types
open Cil
open Visitor

module Q = Queue
module Queue = struct
    type 'a t = 'a Q.t
    let create () = Q.create ()
    let add q e = Q.add e q
    let take q = Q.take q
    let is_empty q = Q.is_empty q
end

module Set_of_hashtbl (H : Hashtbl.S) = struct
    type t = unit H.t
    let create () = H.create 100
    let add t k = H.replace t k ()
    let mem t k = H.mem t k
end

module T_set = Set_of_hashtbl(Cil_datatype.Typeinfo.Hashtbl)
module C_set = Set_of_hashtbl(Cil_datatype.Compinfo.Hashtbl)
module E_set = Set_of_hashtbl(Cil_datatype.Enuminfo.Hashtbl)
module V_set = Set_of_hashtbl(Cil_datatype.Varinfo.Hashtbl)

module State = struct
  type state =
    { types : T_set.t;
      comps : C_set.t;
      enums : E_set.t;
      vars  : V_set.t;
      fun_queue : fundec Queue.t;
      typ_queue : typeinfo Queue.t;
      comp_queue : compinfo Queue.t }
end

module Result = struct
  type result =
    { types : T_set.t;
      comps : C_set.t;
      enums : E_set.t;
      vars  : V_set.t }
end

class relevant_type_visitor { State. types; comps; enums; typ_queue; comp_queue } = object
  inherit frama_c_inplace

  method vtype t =
    begin match t with
      | TNamed (ti, _) ->
          if not (T_set.mem types ti) then begin
            T_set.add types ti;
            Queue.add typ_queue ti
          end
      | TComp (ci, _, _) ->
          if not (C_set.mem comps ci) then begin
            C_set.add comps ci;
            Queue.add comp_queue ci
          end
      | TEnum (ei, _) ->
          E_set.add enums ei
      | _ -> ()
    end;
    DoChildren
end

class relevant_function_visitor { State. vars; fun_queue } add_from_type = object
  inherit frama_c_inplace

  method vvrbl vi =
    if vi.vglob then V_set.add vars vi;
    DoChildren

  method vinst = function
    | Call (_, { enode = Lval (Var vi, NoOffset) }, _, _) ->
        if not (V_set.mem vars vi) then begin
          V_set.add vars vi;
          let kf = Globals.Functions.get vi in
          let open Kernel_function in
          try Queue.add fun_queue (get_definition kf)
          with No_Definition -> List.iter (fun vi -> add_from_type vi.vtype) (get_formals kf)
        end;
        DoChildren
    | _ -> DoChildren

  method vtype t =
    add_from_type t;
    SkipChildren
end

let do_funs funs =
  let { State.
        types;
        comps;
        enums;
        vars;
        fun_queue;
        typ_queue;
        comp_queue } as state =
      { State.
        types = T_set.create ();
        comps = C_set.create ();
        enums = E_set.create ();
        vars = V_set.create ();
        fun_queue = Queue.create ();
        typ_queue = Queue.create ();
        comp_queue = Queue.create () }
  in
  let add_from_type t = ignore (visitFramacType (new relevant_type_visitor state) t) in
  let do_type ti = add_from_type ti.ttype in
  let do_comp ci = List.iter (fun fi -> add_from_type fi.ftype) ci.cfields in
  let do_fun f = ignore (visitFramacFunction (new relevant_function_visitor state add_from_type) f) in
  List.iter (fun fundec ->
               V_set.add vars fundec.svar;
               Queue.add fun_queue fundec)
            funs;
  while not (Queue.is_empty fun_queue) do
    do_fun (Queue.take fun_queue)
  done;
  begin try while true do
    if not (Queue.is_empty typ_queue) then
      do_type (Queue.take typ_queue)
    else if not (Queue.is_empty comp_queue) then
      do_comp (Queue.take comp_queue)
    else
      raise Exit
  done with Exit -> () end;
  { Result. types; comps; enums; vars }

class extractor { Result. types; comps; enums; vars } = object
  inherit frama_c_inplace
  method vglob_aux = function
    | GType (ti, _) when T_set.mem types ti -> SkipChildren
    | GCompTag (ci, _) | GCompTagDecl (ci, _) when C_set.mem comps ci -> SkipChildren
    | GEnumTag (ei, _) | GEnumTagDecl (ei, _) when E_set.mem enums ei -> SkipChildren
    | GVarDecl (_, vi, _) | GVar (vi, _, _) when V_set.mem vars vi -> SkipChildren
    | GFun ( { svar }, _) when V_set.mem vars svar -> SkipChildren
    | GPragma _ -> SkipChildren
    | GText _ -> SkipChildren
    | GAnnot _ -> SkipChildren
    | _ -> ChangeTo []
end

let extract funs =
  let result = do_funs funs in
  fun file ->
  visitFramacFile (new extractor result) file;
  Ast.compute ()

let get_funs () =
  Globals.Functions.fold (fun ({ spec } as kf) acc ->
    if spec.spec_behavior <> [] ||
       spec.spec_variant <> None ||
       spec.spec_terminates <> None ||
       spec.spec_complete_behaviors <> [] ||
       spec.spec_disjoint_behaviors <> [] then
      try Kernel_function.get_definition kf :: acc
      with Kernel_function.No_Definition -> acc
    else acc)
    []
