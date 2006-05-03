(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

open Gobject.Data

exception No_such_prover

type prover = {
  pr_name : string;
  pr_result : int GTree.column;
  pr_icon : GtkStock.id GTree.column;
  pr_id : Dispatcher.prover;
}
  
let cols = new GTree.column_list
let name = cols#add string
let fullname = cols#add string
let parent = cols#add string
let total = cols#add int
let result = cols#add int
  
let first_row = ref None
    
let simplify = {
  pr_name = "Simplify";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_id = Dispatcher.Simplify;
  }
let zenon = {
  pr_name = "Zenon";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_id = Dispatcher.Zenon;
}
let harvey = {
  pr_name = "haRVey";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_id = Dispatcher.Harvey;
}
let cvcl = {
  pr_name = "CVCL";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_id = Dispatcher.Cvcl;
}
  
let provers = [simplify; zenon; harvey; cvcl]
let provers_selected = ref provers
let provers_s = Hashtbl.create 17
let get_provers () = !provers_selected
let _ = assert (List.length provers > 0)


(*
 * Default prover
 *)
let default_prover = ref (List.hd provers)
let get_default_prover () = !default_prover
let set_prover p = 
  if List.mem p !provers_selected 
  then default_prover := p
let print_prover p = p.pr_name
let get_prover s = 
  let rec next = function
    | [] -> 
	raise No_such_prover
    | p' :: r -> 
	if (String.lowercase p'.pr_name) = (String.lowercase s) 
	then p' 
	else next r
  in next !provers_selected

let update_prover_s () = 
  List.iter 
    (fun p -> Hashtbl.add provers_s p "")
    !provers_selected

let add_all_provers () = 
  provers_selected := provers;
  update_prover_s ()

let add_provers l = 
  assert (List.length l > 0);
  provers_selected := 
    List.rev (List.fold_left
      (fun prs pr -> if List.mem pr.pr_name l then pr::prs else prs)
      []
      provers);
  if !provers_selected = [] then 
    begin 
      provers_selected := provers
    end;
  default_prover := List.hd !provers_selected;
  List.iter 
    (fun p -> Hashtbl.add provers_s p "")
    !provers_selected

let affiche () = 
  Hashtbl.iter
    (fun p s -> print_endline p.pr_name)
    provers_s

let select_prover p = 
  if not (Hashtbl.mem provers_s p) then
    Hashtbl.add provers_s p "";
  affiche ()

let deselect_prover p = 
  Hashtbl.remove provers_s p;
  affiche ()

let get_provers_s () = 
  Hashtbl.fold 
    (fun k v acc -> k::acc)
    provers_s
    []
  
(* all obligations *)
let obligs = Hashtbl.create 97
let find_oblig = Hashtbl.find obligs
  
(* obligation name -> its model row *)
let orows = Hashtbl.create 97
(* obligation name -> its failure messages *)
let fwrows = Hashtbl.create 97
  
(* function -> its model row *)
let frows = Hashtbl.create 17 
let find_fct = Hashtbl.find frows
  
(* function -> list of its obligations *)
let fobligs = Hashtbl.create 97
let find_fobligs = Hashtbl.find fobligs
let iter_fobligs fct f = Queue.iter f (Hashtbl.find fobligs fct)
  
(* functions *)
let fq = Queue.create ()
  
let add_failure row (p:prover) (message:string) = 
  try 
    let messages = Hashtbl.find fwrows row in
    if Hashtbl.mem messages p then
      Hashtbl.replace messages p message
    else Hashtbl.add messages p message
  with Not_found -> begin
    let h = Hashtbl.create 97 in
    Hashtbl.add h p message;
    Hashtbl.add fwrows row h
  end

let _ = 
  let h = Hashtbl.create 1 in
  Hashtbl.add h simplify "";
  Hashtbl.add fwrows " " h;
  Hashtbl.clear h;
  Hashtbl.clear fwrows
    
let create_model () =
  let model = GTree.tree_store cols in
  Dispatcher.iter
    (fun ((_,s,_) as o) ->
       Hashtbl.add obligs s o;
       let f,n = Tools.decomp_name s in
       let row =
	 try 
	   Hashtbl.find frows f
	 with Not_found ->
	   let row = model#append () in
	   Queue.add f fq;
	   Hashtbl.add frows f row;
	   Hashtbl.add fobligs f (Queue.create ());
	   model#set ~row ~column:name f;
	   model#set ~row ~column:fullname f;
	   model#set ~row ~column:parent f;
	   model#set ~row ~column:total 0;
	   List.iter 
	     (fun p -> model#set ~row ~column:p.pr_result 0) 
	     provers;
	   row
       in
       let row_n = model#append ~parent:row () in
       (match !first_row with None -> first_row := Some(row_n) | Some _ -> ());
       Hashtbl.add orows s row_n;
       Queue.add row_n (Hashtbl.find fobligs f);
       model#set ~row:row_n ~column:name n;
       model#set ~row:row_n ~column:fullname s;
       model#set ~row:row_n ~column:parent f;
       model#set ~row:row_n ~column:result 0;
       List.iter
	 (fun p -> model#set ~row:row_n ~column:p.pr_icon `REMOVE)
	 provers
    );
  model
    
