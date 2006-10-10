(* oct_anal_core.ml
   All abstract interpreter functions for the example analyzer.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
*)

open Oct_anal_syn
open Oct_anal_lex
open Oct_anal_yacc

let do_debug = ref false;;
let widen_thres = ref 1;; (* begin to widen after that much iterations *)


module type OCT =
sig
  type oct
  type vnum
  type wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum

  val init: unit -> bool
  val empty: int -> oct
  val universe: int -> oct
  val dim: oct -> int
  val is_equal: oct -> oct -> bool
  val add_constraint: oct -> vnum -> oct
  val assign_var: oct -> int -> vnum -> oct
  val union: oct -> oct -> oct
  val widening: oct -> oct -> wident -> oct
  val close: oct -> oct
  val foctprinter: (int -> string) -> Format.formatter -> oct -> unit
  val memprint: unit -> unit
  val timeprint: unit -> unit
  val forget: oct -> int -> oct
  val vnum_of_float: float array -> vnum
end



(* polyhedra module *)
(* **************** *)

(* this compatibility module redefines Oct to call the New Polka library,
   so that you can use polyhedra instead of Octagons in the following 

   BEWARE: it will only work if configure can find OCaml's binding for
   NewPolka!
*)

(*
module PolyOct = (struct
  
  type oct = Poly.t
  type vnum = Vector.t
  type wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum

  let init ()        = Polka.initialize false 10000 100; true
  let empty          = Poly.empty
  let universe       = Poly.universe
  let dim            = Poly.dim
  let is_equal       = Poly.is_equal
  let add_constraint = Poly.add_constraint
  let assign_var     = Poly.assign_var
  let union          = Poly.union
  let widening x y _ = Poly.widening x y
  let close x        = x
  let foctprinter    = Poly.print_constraints
  let memprint ()    = ()
  let timeprint ()   = ()

  let forget t i = 
    let d = [| { Vector.pos = i; Vector.nbdims = 1; } |] in
    Poly.add_dims_and_embed_multi (Poly.del_dims_multi t d) d
    

  let tresh = 1000000.

  let vnum_of_float a =
    let v = Vector.make ((Array.length a)+ !Polka.dec-1) in
    Vector.set v 0 (int_of_float tresh);
    Vector.set v 1 (int_of_float (tresh*.a.((Array.length a)-1)));
    for i=0 to (Array.length a)-2 do
      Vector.set v (i+(!Polka.dec)) (int_of_float (tresh*.a.(i)))
    done;
    v
end:OCT);;
*)
    
module Analyze (Oct: OCT) =
struct


let init () = ignore(Oct.init())

let quit () = Oct.memprint (); Oct. timeprint ()


(* transform a character position into a (line,column) position *)
let location_of_pos pos =
  let rec search =
    function
      (posl, ln)::_ when posl<=pos -> (ln, (pos-posl))
    | _::t -> search t
    | [] -> failwith ("Internal error in location_of_pos "^(string_of_int pos))
  in search !line_offsets


(* expression transformation *)
(* ************************* *)

(* get the list of variables used in an instruction block as a hashtable
   variable name -> variable index (starting from 0), a list of variable 
   names, and the number of variables
*)
let get_varlist b =
  let h = Hashtbl.create 1
  and vv = ref []
  and n = ref 0 in

  let add v =
   if not (Hashtbl.mem h v)
   then begin vv:=v::(!vv); Hashtbl.add h v !n; incr n end in

  let rec vinst = function
      ASSIGN (s,e) -> add s; viexpr e
    | ASSERT b     -> vbexpr b
    | IF (a,b)     -> vbexpr a; vblock b
    | IF2 (a,b,c)  -> vbexpr a; vblock b; vblock c
    | LOOP (a,b)   -> vbexpr a; vblock b
  and viexpr = function
      VAR s        -> add s
    | PLUS (a,b)   -> viexpr a; viexpr b
    | MINUS (a,b)  -> viexpr a; viexpr b
    | TIMES (a,b)  -> viexpr a; viexpr b
    | _            -> ()
  and vbexpr = function
      AND (a,b)    -> vbexpr a; vbexpr b
    | OR (a,b)     -> vbexpr a; vbexpr b
    | NOT a        -> vbexpr a
    | COMP (_,a,b) -> viexpr a; viexpr b
    | _            -> ()
  and vblock = function (_,l) -> 
    let rec toto = function 
	[]       -> ()
      |	(a,_)::l -> vinst a; toto l
    in toto l

  in vblock b; (h,(List.rev !vv),!n)


(* "flatify" a arithmetic expression into
   - either a linear expression
   - a random expression
*)

type flatiexpr =
    FIRAND                   (* random expression *)
  | FLINEAR of float array   (* linear expression *)

let parse_iexpr e (v,n) =
  let rec randup = function
      TIMES(a,b) -> (match (randup a,randup b) with
      	(FIRAND,_)  | (_,FIRAND)  -> FIRAND
      |	(FLINEAR a1,FLINEAR a2) ->
	  try
	    for i=0 to n-1 do if a1.(i)<>0. then raise Not_found done;
	    let t = Array.make (n+1) 0.
	    in for i=0 to n do t.(i) <- a1.(n) *. a2.(i) done; FLINEAR t
	  with Not_found ->
	    try
	      for i=0 to n-1 do if a2.(i)<>0. then raise Not_found done;
	      let t = Array.make (n+1) 0.
	      in for i=0 to n do t.(i) <- a2.(n) *. a1.(i) done; FLINEAR t
	    with Not_found -> FIRAND)
    | PLUS(a,b) -> (match (randup a,randup b) with
	(FIRAND,_) | (_,FIRAND) -> FIRAND
      |	(FLINEAR a1,FLINEAR a2) ->
	  let t = Array.make (n+1) 0. in
	  for i=0 to n do t.(i) <- a1.(i) +. a2.(i) done; FLINEAR t)
    | MINUS(a,b) -> (match (randup a,randup b) with
	(FIRAND,_) | (_,FIRAND) -> FIRAND
      |	(FLINEAR a1,FLINEAR a2) ->
	  let t = Array.make (n+1) 0. in
	  for i=0 to n do t.(i) <- a1.(i) -. a2.(i) done; FLINEAR t)
    | CST c -> let t = Array.make (n+1) 0. in t.(n) <- c; FLINEAR t
    | RAND  -> FIRAND
    | VAR s -> let t = Array.make (n+1) 0. in t.(Hashtbl.find v s) <- 1.; FLINEAR t

  in randup e


(* simplify a boolean expression by
   - propagating random upward
   - propagating not to the leaves
   - using and / or associativity
   - canonizing tests
 *)

type flatbexpr =
    FBRAND                   (* random expression *)
  | FBAND of flatbexpr list  (* and *)
  | FBOR  of flatbexpr list  (* or *)
  | FTEST of float array       (* linear test *)
  | FTRUE | FFALSE           (* constant expression *)

let parse_bexpr b (v,n) = 
  let rec simpl = function
      AND (a,b) -> (match (simpl a,simpl b) with
      	(FFALSE,_) | (_,FFALSE) -> FFALSE
      |	(FTRUE,a) -> a | (a,FTRUE) -> a
      |	(FBRAND,_) | (_,FBRAND) -> FBRAND
      |	(FBAND l1,FBAND l2) -> FBAND (l1@l2)
      |	(FBAND l,a) -> FBAND (a::l)
      |	(a,FBAND l) -> FBAND (a::l)
      |	(a,b) -> FBAND [a;b]
	    )
    | OR (a,b) -> (match (simpl a,simpl b) with
	(FTRUE,_) | (_,FTRUE) -> FTRUE
      |	(FFALSE,a) -> a | (a,FFALSE) -> a
      |	(FBRAND,_) | (_,FBRAND) -> FBRAND
      |	(FBOR l1,FBOR l2) -> FBOR (l1@l2)
      |	(FBOR l,a) -> FBOR (a::l)
      |	(a,FBOR l) -> FBOR (a::l)
      |	(a,b) -> FBOR [a;b]
	    )

    | NOT (AND(a,b)) -> simpl (OR (NOT a,NOT b))
    | NOT (OR(a,b))  -> simpl (AND(NOT a,NOT b))
    | NOT (NOT a)    -> simpl a
    | NOT (COMP (LESS,a,b))      -> simpl (COMP(GREATEREQ,a,b))
    | NOT (COMP (LESSEQ,a,b))    -> simpl (COMP(GREATER,a,b))
    | NOT (COMP (GREATER,a,b))   -> simpl (COMP(LESSEQ,a,b))
    | NOT (COMP (GREATEREQ,a,b)) -> simpl (COMP(LESS,a,b))
    | NOT (COMP (EQ,a,b))        -> simpl (COMP(NOTEQ,a,b))
    | NOT (COMP (NOTEQ,a,b))     -> simpl (COMP(EQ,a,b))

    | BRAND          -> FBRAND
    | TRUE           -> FTRUE
    | FALSE          -> FFALSE
    | NOT (BRAND)    -> FBRAND
    | NOT (TRUE)     -> FFALSE
    | NOT (FALSE)    -> FTRUE

    | COMP (EQ,a,b)    -> FBAND [simpl (COMP (LESSEQ,a,b)); simpl (COMP(GREATEREQ,a,b))]
    | COMP (NOTEQ,a,b) -> FBOR  [simpl (COMP (LESS,a,b))  ; simpl (COMP(GREATER  ,a,b))]
    | COMP (GREATER,a,b)   -> simpl (COMP (LESS,b,a))
    | COMP (GREATEREQ,a,b) -> simpl (COMP (LESSEQ,b,a))
    | COMP (LESS,a,b)      -> simpl (COMP (LESSEQ,a,MINUS(b,CST 1.)))
(*    | COMP (LESS,a,b)      -> simpl (COMP (LESSEQ,a,b))*)

    | COMP (LESSEQ,a,b) -> match (parse_iexpr a (v,n),parse_iexpr b (v,n)) with
	(FIRAND,_) | (_,FIRAND) -> FBRAND
      |	(FLINEAR a1,FLINEAR a2) ->
	let t = Array.make (n+1) 0.
	in for i=0 to n do t.(i) <- a2.(i) -. a1.(i) done; FTEST t

  in simpl b


(* pretty-printing expression *)


let flatiexpr_to_string expr var = match expr with
    FIRAND    -> "?"
  | FLINEAR f -> 
      let s = ref "" in
      for i=0 to (Array.length f)-2 do
	if f.(i) <> 0. then
	  if !s="" then s:=(string_of_float f.(i))^"*"^var.(i)
	  else s:=(!s)^" + "^(string_of_float f.(i))^"*"^var.(i)
      done;
      if f.((Array.length f)-1) <> 0. then
	if !s="" then s:=(string_of_float f.((Array.length f)-1))
        else s:=(!s)^" + "^(string_of_float f.((Array.length f)-1));
      if !s="" then s:="0";
      !s
 
let flatbexpr_to_string expr var = 
  let rec toto = function
      FBRAND  -> "?"
    | FBAND [] -> ""
    | FBOR [] -> ""
    | FBAND (a::l) -> 
	"("^(List.fold_left (fun a b -> a^" & "^(toto b)) (toto a) l)^")"
    | FBOR (a::l) -> 
	"("^(List.fold_left (fun a b -> a^" | "^(toto b)) (toto a) l)^")"
    | FTRUE -> "true"
    | FFALSE -> "false"
    | FTEST f -> 
	let s = ref "" in
	for i=0 to (Array.length f)-2 do
	  if f.(i) <> 0. then
	    if !s="" then s:=(string_of_float f.(i))^"*"^var.(i)
	    else s:=(!s)^" + "^(string_of_float f.(i))^"*"^var.(i)
	done;
	if f.((Array.length f)-1) <> 0. then 
	  if !s="" then s:=(string_of_float f.((Array.length f)-1))
          else s:=(!s)^" + "^(string_of_float f.((Array.length f)-1));
	if !s="" then s:="0";
	!s^">=0"

  in toto expr


let iexpr_to_string e =
  let rec toto = function 
      VAR s -> s
    | RAND -> "rand"
    | CST i -> string_of_float i
    | TIMES(a,b) -> "("^(toto a)^"*"^(toto b)^")"
    | PLUS (a,b) -> "("^(toto a)^"+"^(toto b)^")"
    | MINUS(a,b) -> "("^(toto a)^"-"^(toto b)^")"
  in toto e


let bexpr_to_string e =
  let rec toto = function 
      TRUE  ->  "true"
    | FALSE -> "false"
    | BRAND -> "rand"
    | AND (a,b) -> "("^(toto a)^" && "^(toto b)^")"
    | OR  (a,b) -> "("^(toto a)^" || "^(toto b)^")"
    | NOT a     -> "~("^(toto a)^")"
    | COMP (c,a,b) -> (iexpr_to_string a)^(match c with
	LESS -> "<"
      |	LESSEQ -> "<="
      |	GREATER -> ">"
      |	GREATEREQ -> ">="
      |	EQ -> "="
      |	NOTEQ -> "<>")^(iexpr_to_string b)
  in toto e


(* control flow graph *)
(* ****************** *)

(* nodes can be
   - control point nodes that embed an abstract state
   - a transfer funcion node that propagates information from a control
   point to another one
*)

(* control point nodes *)
type statetype = 
    NormalNode
  | EntryNode (* entry control point *)
  | ExitNode  (* exit control point *)
  | BackNode  (* control point before an end-of-loop *)

and showtype =
    ShowNormal 
  | ShowHide
  | ShowEnd  (* used at the end of an if *)
    
and statenode = 
    { mutable state : Oct.oct;
      state_id      : int;   (* unique identifier *)
      ctrlpt        : int;   (* offset of the control point in the source *)

      mutable show  : showtype; (* used when printing *)

      (* these three are mutable, not because they change value, but because 
	 the correct value is known way after the struct is created ! 
	 a state node has only one successor, and one predecessor
	 (except for ExitNode/EntryNode that may have none)
      *)
      mutable state_type  : statetype;
      mutable state_pre   : funcnode option;
      mutable state_post  : funcnode option;

      mutable dirty : bool;   (* used by the worklist algorithm *)
    } 
      
(* transfer function nodes *)
and functype =
    AssignNode of assign_node
  | AssertNode of assert_node
  | IfNode     of if_node
  | JoinNode   of join_node
  | LoopNode   of loop_node

and assign_node =
    { assign_pre:   statenode;
      assign_post:  statenode;
      assign_var:   int;
      assign_expr:  flatiexpr;
    } 

and assert_node =
    { assert_pre:   statenode;
      assert_post:  statenode;
      assert_expr:  flatbexpr;
    } 

and if_node =
    { if_pre:         statenode;
      if_post_true:   statenode;
      if_post_false:  statenode;
      if_expr_true:   flatbexpr;
      if_expr_false:  flatbexpr;
    } 

and join_node =
    { join_pre1:  statenode;
      join_pre2:  statenode;
      join_post:  statenode;
    } 

and loop_node =
    { loop_pre_init:  statenode;
      loop_pre_loop:  statenode;
      loop_post_loop: statenode;
      loop_post_exit: statenode;
      loop_expr_loop: flatbexpr;
      loop_expr_exit: flatbexpr;
      mutable loop_iter: int;
    } 

and funcnode =
    { label:   string;
      func_id: int;           (* unique identifier *)
      func:    functype
    } 

(* construct the control flow graph 
   return a list of statenode and a list of funcnode *)
let concrete_to_graph c (v,n) =
  let id = ref 0
  and id2 = ref 0 in
  
  let new_statenode i =
    incr id2; { state = Oct.empty n; ctrlpt = i; state_id = !id2; 
		state_type = NormalNode; dirty = false;  show = ShowNormal;
		state_pre = None; state_post = None }

  and new_funcnode f l =
    incr id; { func_id = !id;  func = f; label = l; }
  in
      
  let rec ginst inst pre post = match inst with
    ASSIGN (s,e) ->
      let f = new_funcnode (AssignNode { assign_pre = pre;
					 assign_post = post;
					 assign_var = Hashtbl.find v s;
					 assign_expr = parse_iexpr e (v,n) })
	  (s^" := "^(iexpr_to_string e))
      in
      pre.state_post <- Some f;
      post.state_pre <- Some f;
      ([],[f])

  | ASSERT e ->
      let f = new_funcnode (AssertNode { assert_pre = pre;
					 assert_post = post;
					 assert_expr = parse_bexpr e (v,n) })
	  ((bexpr_to_string e)^" ?")
      in      
      pre.state_post <- Some f;
      post.state_pre <- Some f;
      ([],[f])

  | IF (e,b1) ->
      let (sn1,fn1,pre1,post1) = gblock b1 in
      let pre2 = new_statenode post1.ctrlpt in
      let f = new_funcnode (IfNode { if_pre = pre;
				     if_post_true  = pre1;
				     if_post_false = pre2;
				     if_expr_true  = parse_bexpr e (v,n);
				     if_expr_false = parse_bexpr (NOT e) (v,n);
				   })
	  ((bexpr_to_string e)^" ?")
      and j = new_funcnode (JoinNode { join_pre1 = post1;
				       join_pre2 = pre2;
				       join_post = post; }) "U"
      in
      pre2.show <- ShowHide;
      post.show <- ShowEnd;
      pre.state_post <- Some f;
      pre1.state_pre <- Some f;
      pre2.state_pre <- Some f;
      post1.state_post <- Some j;
      pre2.state_post  <- Some j;
      post.state_pre   <- Some j;
      (pre2::sn1,f::j::fn1)

  | IF2 (e,b1,b2) ->
      let (sn1,fn1,pre1,post1) = gblock b1
      and (sn2,fn2,pre2,post2) = gblock b2 in
      let f = new_funcnode (IfNode { if_pre = pre;
				     if_post_true  = pre1;
				     if_post_false = pre2;
				     if_expr_true  = parse_bexpr e (v,n);
				     if_expr_false = parse_bexpr (NOT e) (v,n);
				   })
	  ((bexpr_to_string e)^" ?")
      and j = new_funcnode (JoinNode { join_pre1 = post1;
				       join_pre2 = post2;
				       join_post = post; }) "U"
      in
      post.show <- ShowEnd;
      pre.state_post <- Some f;
      pre1.state_pre <- Some f;
      pre2.state_pre <- Some f;
      post1.state_post <- Some j;
      post2.state_post <- Some j;
      post.state_pre   <- Some j;
      (sn1@sn2,f::j::(fn1@fn2))

  | LOOP (e,b) ->
      let (sn1,fn1,pre1,post1) = gblock b in
      let f = new_funcnode (LoopNode { loop_pre_init  = pre;
				       loop_pre_loop  = post1;
				       loop_post_loop = pre1;
				       loop_post_exit = post;
				       loop_expr_loop = parse_bexpr e (v,n);
				       loop_expr_exit = parse_bexpr (NOT e) (v,n);
				     loop_iter = 0 })
	  ((bexpr_to_string e)^" ?")
      in
      post1.show <- ShowEnd;
      pre.state_post   <- Some f;
      pre1.state_pre   <- Some f;
      post1.state_post <- Some f;
      post.state_pre   <- Some f;
      post1.state_type <- BackNode;
      (sn1,f::fn1)

  and gblock = function (p,l) ->
    let pre = new_statenode p in
    let rec next l pre = match l with
      [] -> ([pre],[],pre)
    | (i,p)::l -> 
	let post = new_statenode p in 
	let (sn1,fn1) = ginst i pre post
	and (sn2,fn2,postend) = next l post
	in (pre::(sn1@sn2),fn1@fn2,postend)
    in let (a,b,post) = next l pre in (a,b,pre,post)
      
  in let (a,b,pre,post) = gblock c in 
  post.state_type <- ExitNode;  pre.state_type <- EntryNode; 
  (a,b,pre,post)




(* print results *)
(* ************* *)

(* ugly terminal command => used to underline / boldify a part of the code *)
let enter_bold = "\027[4m\027[1m"
let leave_bold = "\027[m"

(* prints the original sourcecode with a part underlined *)
let print_underline textout s l1 c1 l2 c2 = 
  let (l,c) = (ref 1,ref 0) in
  let put a =
    if !l=l1 && !c=c1 then output_string textout enter_bold;
    output_char textout a;
    if !l=l2 && !c=c2 then output_string textout leave_bold;
    incr c;
    if a='\n' then begin c:=0; incr l end
  in 
  Stream.iter put (Stream.of_string s);
  output_string textout leave_bold;
  output_string textout "\n";
  flush textout


let output_html_char out = function
    '&' -> output_string out "&amp;"
  | '"' -> output_string out "&quot;"
  | '<' -> output_string out "&lt;"
  | '>' -> output_string out "&gt;"
  | a -> output_char out a


(* same, but in HTML format *)
let print_html_underline out s l1 c1 l2 c2 = 
  output_string out "<pre>\n";
  let (l,c) = (ref 1,ref 0) 
  and o = ref false in
  let put a =
    if !l=l1 && !c=c1 && not !o
    then begin o:=true; output_string out "<font color=\"#BC8F8F\">" end;
    output_html_char out a;
    if !l=l2 && !c=c2 && !o
    then begin o:=false; output_string out "</font>" end;
    incr c;
    if a='\n' then begin c:=0; incr l end
  in 
  Stream.iter put (Stream.of_string s);
  if !o then output_string out "</font>";
  output_string out "\n</pre>\n";
  flush out



(* prints a control-flow graph in gdl format (AiSee) *)

let print_graph_header s =
  output_string s "graph: { title: \"ControlFlowGraph\"\n\n";
  output_string s ("  manhattan_edges: yes\n"^
		   "  port_sharing: no\n"^
		   "  finetuning: no\n"^
		   "  layout_downfactor: 100\n"^
		   "  layout_upfactor: 0\n"^
		   "  layout_nearfactor: 0\n"^
		   "  straight_phase: yes\n"^
		   "  priority_phase: yes\n"^
		   "  display_edge_labels: yes\n"^
		   "  yspace: 40\n"^
		   "  xspace: 80\n\n");
  flush s


let print_graph_footer s = 
  output_string s "\n}\n";
  flush s
 

let print_graph s name var (sn,fn,pre,post) =

  let f = Format.formatter_of_out_channel s
  and var2 = Array.of_list var in

  let string_of_id d = "_"^name^"_"^(string_of_int d) in

  (* header *)
  Printf.fprintf s "graph: { title: \"%s\"\n\n" name;

  (* controlpoint nodes  *)

  output_string s ("  node.shape: ellipse\n"^
		   "  node.label: \"\"\n"^
		   "  node.color: 28\n"^
		   "  node.bordercolor: 9\n"^
		   "  node.scaling: 0.75\n\n");

  List.iter (function a ->
    let (l,c) = location_of_pos a.ctrlpt in
    Printf.fprintf s "  node: { title: \"CtrlPt%s\"\n" 
      (string_of_id a.state_id);
    Printf.fprintf s "          info1: \"line %d, column %d,char %d\\n"
      l c a.ctrlpt;
    Oct.foctprinter (fun i -> var2.(i)) f (Oct.close a.state);
    Format.pp_print_flush f ();
    output_string s "\" ";
    if a.state_type = EntryNode (* entry node *)
    then begin
      output_string s ("vertical_order: 0 "^
		       "shape: ellipse color: 28 "^
		       "bordercolor: 9 "^
		       "borderwidth: 6 ");
      Printf.fprintf s "label: \"entry (%d)\"  " a.state_id
    end
    else if a.state_type = ExitNode (* exit node *)
    then begin
      output_string s ("vertical_order: 0 "^
		       "shape: ellipse color: 28 "^
		       "bordercolor: 9 "^
		       "borderwidth: 6 ");
      Printf.fprintf s "label: \"exit (%d)\"  " a.state_id
    end
    else Printf.fprintf s "label: \"(%d)\" " a.state_id; (* normal node *)
    output_string s "}\n";
    ) sn;


  (* transfer function nodes *)

  Printf.fprintf s "\n  node.scaling: 1.0\n  edge.textcolor: 10\n\n";
  
  (* edges from a transfer function to a control point node *)
  let emit_edge_post fu st lbl bent =
    output_string s  "    ";
    if st.state_type = BackNode then output_string s "backedge:     { "
    else if bent then                output_string s "bentnearedge: { " 
    else                             output_string s "edge:         { " ;
    Printf.fprintf s "targetname: \"CtrlPt%s\" " (string_of_id st.state_id);
    Printf.fprintf s "sourcename: \"Func%s\" " (string_of_id fu.func_id);
    output_string  s "arrowstyle: none ";
    if lbl<>"" then Printf.fprintf s "label: \"%s\" " lbl;
    output_string s "}\n"
  in

  (* edge from a control point to a transfer function node *)
  let emit_edge_pre fu st =
    output_string s  "    ";
    if st.state_type = BackNode then output_string s "backedge:     { "
    else                             output_string s "edge:         { " ;
    Printf.fprintf s "sourcename: \"CtrlPt%s\" " (string_of_id st.state_id);
    Printf.fprintf s "targetname: \"Func%s\" " (string_of_id fu.func_id);
    output_string  s "}\n"
  in

  let emit_func f =
    Printf.fprintf s "  node: { title: \"Func%s\" label: \" %s \" "
      (string_of_id f.func_id) f.label;
    match f.func with
      AssignNode fu ->
	output_string  s "shape: box color:19 bordercolor: 11 ";
	Printf.fprintf s "info1: \"assign: %s <- %s \" }\n"
	  var2.(fu.assign_var) (flatiexpr_to_string fu.assign_expr var2);
	emit_edge_pre  f fu.assign_pre;
	emit_edge_post f fu.assign_post "" false

    | AssertNode fu ->
	output_string  s "shape: rhomb color:18 bordercolor: 10 ";
	Printf.fprintf s "info1: \"assert: %s\" }\n"
	  (flatbexpr_to_string fu.assert_expr var2);
	emit_edge_pre  f fu.assert_pre;
	emit_edge_post f fu.assert_post "assert" false

    | IfNode fu ->
	output_string  s "shape: rhomb color:18 bordercolor: 10 ";
	Printf.fprintf s "info1: \"true:  %s\\nfalse: %s\" }\n"
	  (flatbexpr_to_string fu.if_expr_true var2)
	  (flatbexpr_to_string fu.if_expr_false var2);
	emit_edge_pre  f fu.if_pre;
	emit_edge_post f fu.if_post_true  "true"  true;
	emit_edge_post f fu.if_post_false "false" true
	
    | LoopNode fu ->
	output_string  s "shape: rhomb color:18 bordercolor: 10 ";
	Printf.fprintf s "info1: \"loop: %s\\nexit: %s\" }\n"
	  (flatbexpr_to_string fu.loop_expr_loop var2)
	  (flatbexpr_to_string fu.loop_expr_exit var2);
	emit_edge_pre  f fu.loop_pre_init;
	emit_edge_pre  f fu.loop_pre_loop;
	emit_edge_post f fu.loop_post_loop "loop" false;
	emit_edge_post f fu.loop_post_exit "exit" true;
	
    | JoinNode fu ->
	output_string  s "shape: ellipse color:19 bordercolor: 11 "; 
	Printf.fprintf s "info1:\"join\" }\n";
	emit_edge_pre  f fu.join_pre1;
	emit_edge_pre  f fu.join_pre2;
	emit_edge_post f fu.join_post "" false

  in List.iter emit_func fn;
  
  (* footer *)
  output_string s "\n}\n\n";
  flush s
    
    
(* how to sort control-points to display them at the right position in
   the original source-code ?
   when two control-points have the same character offset (after a if/then/else
   statement), display the one with greatest id first, it corresponds to the 
   end of innermost block 
*)
let compare_ctrlpt a b =
  if a.ctrlpt - b.ctrlpt <> 0 then a.ctrlpt - b.ctrlpt
  else b.state_id - a.state_id
    
(* prints the original sourcecode with the control points *)
let print_ctrlpoints out s name (sn,fn,pre,post) bold = 
  let c = ref 0        (* current position *)
  and cp = ref (List.sort compare_ctrlpt sn) (* remaining control points *)
  and newline = ref true
  and line = ref 0
  in
  let put a = (* put one char, and possibly control point name *)
    if !c >= pre.ctrlpt && !c <= post.ctrlpt then
      begin
	if !newline then begin 
	  newline:=false; 
	  Printf.fprintf out "%-5i " !line 
	end;
	let fin = ref false in
	while not !fin do
	  (match !cp with
	    a::l when a.ctrlpt <= !c ->
	      (match a.show with
		ShowNormal ->
		  Printf.fprintf out " %s(%d)%s " 
		    (if bold then enter_bold else "") 
		    a.state_id 
		    (if bold then leave_bold else "")
	      |	ShowEnd ->
		  Printf.fprintf out " %s[%d]%s " 
		    (if bold then enter_bold else "") 
		    a.state_id 
		    (if bold then leave_bold else "")
	      |	_ -> () );
	      cp:=l
	  |  _ -> fin:=true );
	done;
	output_char out a;
      end;
    incr c;
    if a='\n' then begin newline:=true; incr line end
  in 
  Printf.fprintf out "program %s\n" name;
  Stream.iter put (Stream.of_string s);
  output_string out "\n";
  flush out


(* the same but in html format *)
let print_html_ctrlpoints out s name (sn,fn,pre,post) = 
  let c = ref 0        (* current position *)
  and cp = ref (List.sort compare_ctrlpt sn) (* remaining control points *)
  and newline = ref true
  and line = ref 0
  in
  let put a = (* put one char, and possibly control point name *)
    if !c >= pre.ctrlpt && !c <= post.ctrlpt then
      begin
	if !newline then begin 
	  newline:=false; 
	  Printf.fprintf out "<font color=\"#108010\">%-5i </font>" !line 
	end;
	let fin = ref false in
	while not !fin do
	  (match !cp with
	    a::l when a.ctrlpt <= !c ->
	      (match a.show with
		ShowNormal ->
		  Printf.fprintf out " <a href=\"#CtrlPt%s%d\">(%d)</a> " 
		    name a.state_id a.state_id
	      |	ShowEnd ->
		      Printf.fprintf out " <a href=\"#CtrlPt%s%d\">[%d]</a> " 
		name a.state_id a.state_id
	      |	_ -> () );
	      cp:=l
	  |  _ -> fin:=true );
	done;
	output_html_char out a;
      end;
    incr c;
    if a='\n' then begin newline:=true; incr line end
  in 
  Printf.fprintf out "<br><a name=\"Prog%s\"><h2>Program %s</h2></a>\n<pre>\n" name name;
  Stream.iter put (Stream.of_string s);
  output_string out  "</pre>\n";
  flush out

(* print the invariant discovered at each control point *)
let print_result out name var (sn,fn,pre,post) bold = 
  let sn2 = List.sort compare_ctrlpt sn 
  and f = Format.formatter_of_out_channel out 
  and var2 = Array.of_list var in
  Format.pp_set_formatter_output_functions f
    (fun s p n -> for i=p to p+n-1 do output_char out s.[i] done)
    (fun () -> flush out);
  List.iter (function a ->
    let (l,c) = location_of_pos a.ctrlpt in
    Printf.fprintf out "Control point %s%s(%d)%s " name 
      (if bold then enter_bold else "") a.state_id
      (if bold then leave_bold else "");
    Printf.fprintf out "(line %d, column %d, character %d)\n" 
      l c a.ctrlpt;
    Oct.foctprinter (fun i -> var2.(i)) f (Oct.close a.state);
    Format.pp_print_flush f ();
    Printf.fprintf out "\n\n"
      ) sn2;
  Printf.fprintf out "\n";
  flush out
    

(* the same, but in HTML *)
let print_html_result out name var (sn,fn,pre,post) = 
  let sn2 = List.sort compare_ctrlpt sn 
  and f = Format.formatter_of_out_channel out 
  and var2 = Array.of_list var in
  Format.pp_set_formatter_output_functions f
    (fun s p n -> for i=p to p+n-1 do output_html_char out s.[i] done)
    (fun () -> flush out);
  List.iter (function a ->
    let (l,c) = location_of_pos a.ctrlpt in
    Printf.fprintf out "<br><a name=\"CtrlPt%s%d\">\n" name a.state_id;
    Printf.fprintf out "<h3>Control point %s(%d)</h3></a>\n" name a.state_id;
    Printf.fprintf out "<p>line %d, column %d, character %d</p>\n<pre>" 
      l c a.ctrlpt;
    Oct.foctprinter (fun i -> var2.(i)) f (Oct.close a.state);
    Format.pp_print_flush f ();
    Printf.fprintf out "</pre>\n<a href=\"#Prog%s\">back to the program source</a><br><hr>\n" name
      ) sn2;
  flush out
    

let print_html_header out =
  output_string out "<html><head><title>Totor</title></head><body>\n";
  flush out

let print_html_footer out =
  output_string out "</body></html>\n";
  flush out
    
    
    
(* parser *)
(* ****** *)

(* parse a string and return the concrete tree *)
let string_to_concrete textout htmlout s =
  let lexbuf = Lexing.from_string s in

  let error_extent lexbuf =
    (location_of_pos (Lexing.lexeme_start lexbuf)),
    (location_of_pos (Lexing.lexeme_end lexbuf)) in

  try proglist token lexbuf with 
    
    Parsing.Parse_error ->
      let ((l1,c1),(l2,c2)) = error_extent lexbuf in
      Printf.fprintf textout
        "Parse error near \"%s\" begining at line %d, column %d, ending at line %d, column %d\n\n"
        (Lexing.lexeme lexbuf) l1 c1 l2 c2;      
      print_underline textout s l1 c1 l2 c2;
      Printf.fprintf htmlout "<p><color= \"#800\">Parse error</color></p>\n";
      print_html_underline htmlout s l1 c1 l2 c2;
      flush textout; flush htmlout;
      failwith "Error #1"
        
  | Failure "lexing: empty token" ->
      let ((l1,c1),(l2,c2)) = error_extent lexbuf in
      Printf.fprintf textout
        "Lexical error begining at line %d, column %d, ending at line %d, column %d\n\n"
        l1 c1 l2 c2;
      print_underline textout s l1 c1 l2 c2;
      Printf.fprintf htmlout "<p><color= \"#800\">Lexical error</color></p>\n";
      print_html_underline htmlout s l1 c1 l2 c2;
      flush textout; flush htmlout;
      failwith "Error #2"
        
  | Failure "int_of_string" ->
      let ((l1,c1),(l2,c2)) = error_extent lexbuf in
       Printf.fprintf textout
        "Invalid integer constant \"%s\" begining at line %d, column %d, ending at line %d, column %d\n\n"
        (Lexing.lexeme lexbuf) l1 c1 l2 c2;
      print_underline textout s l1 c1 l2 c2;
      Printf.fprintf htmlout "<p><color= \"#800\">Invalid integer constant</color></p>\n";
      print_html_underline htmlout s l1 c1 l2 c2;
      flush textout; flush htmlout;
      failwith "Error #3"

  | Unterminated_comment i ->
      let (l,c) = location_of_pos i in
      Printf.fprintf textout
	"Unterminated comment, starting at line %d, column %d\n\n" l c;
      print_underline textout s l c l (c+2);
      Printf.fprintf htmlout "<p><color= \"#800\">Unterminated comment</color></p>\n";
      print_html_underline htmlout s l c l (c+2);
      flush textout; flush htmlout;
      failwith "Error #4"
        

(* read all the contents of the stream s, return the result as a big string *)
let stream_to_string s =
  let b = Buffer.create 16 in
  (try
    while true do
      Buffer.add_string b (input_line s);
      Buffer.add_char b '\n'
    done
  with End_of_file -> ());
  Buffer.contents b



(* analysis *)
(* ******** *)


let analyze_graph debug var (sn,fn,pre,post) = 
  let worklist = ref [] (* dirty state nodes that need to be propagated *)
  and n = Oct.dim pre.state in
 
  let f = Format.formatter_of_out_channel debug 
  and var2 = Array.of_list var 
  and maxl = ref 0 in
 
  let set s v =
    if not (Oct.is_equal s.state v) then begin
      s.state <- v;
      if !do_debug then begin
	Printf.fprintf debug "update (%i) <- " s.state_id;
(*	Oct.foctprinter (fun i -> var2.(i)) f s.state;
        Format.pp_print_flush f ();
	Printf.fprintf debug " / "; *)
	Oct.foctprinter (fun i -> var2.(i)) f (Oct.close s.state);
	Format.pp_print_flush f ();
	Printf.fprintf debug "\n"
      end;
      if not s.dirty then begin s.dirty <-true; worklist := (!worklist)@[s] end
    end 
    else if !do_debug then
      begin
	Printf.fprintf debug "unchanged (%i)  = " s.state_id;
(*	Oct.foctprinter (fun i -> var2.(i)) f s.state;
	Format.pp_print_flush f ();
	Printf.fprintf debug " / "; *)
	Oct.foctprinter (fun i -> var2.(i)) f (Oct.close s.state);
	Format.pp_print_flush f ();
	Printf.fprintf debug "\n"
      end

  and undirty b = b.dirty <- false
  in
  
  (* eval forward a flatbexpr *)
  let rec beval s = function
      FBRAND
    | FTRUE    -> s
    | FFALSE   -> Oct.empty n
    | FBAND  l -> List.fold_left beval s l
    | FTEST  f -> Oct.add_constraint s (Oct.vnum_of_float f)
    | FBOR   l ->
	let rec toto = function
	    []    -> failwith "invalid control flow graph #5"
	  | e::[] -> beval s e
	  | e::l  -> Oct.union (beval s e) (toto l)
	in toto l
  in
  
  (* eval forward a transfer function *)
  let eval a = 
    if !do_debug then Printf.fprintf debug "eval '%s'\n" a.label;
    match a.func with

    AssignNode f ->
      (match f.assign_expr with
	FIRAND ->
	  undirty f.assign_pre;
	  set f.assign_post (Oct.forget f.assign_pre.state f.assign_var)
	  
      |	FLINEAR i ->
	  undirty f.assign_pre;
	  set f.assign_post
	    (Oct.assign_var f.assign_pre.state f.assign_var (Oct.vnum_of_float i))
	    )

  | IfNode f ->
      undirty f.if_pre;
      set f.if_post_true (beval f.if_pre.state f.if_expr_true);
      set f.if_post_false (beval f.if_pre.state f.if_expr_false)

  | AssertNode f ->
      undirty f.assert_pre;
      set f.assert_post (beval f.assert_pre.state f.assert_expr)

  | JoinNode f ->
      undirty f.join_pre1;
      undirty f.join_pre2;
      set f.join_post (Oct.union f.join_pre1.state f.join_pre2.state)
	
  | LoopNode f ->
      (* widening is on node loop_post_loop (first control point _in_ the loop)
	 when it is stabilized, update loop_post_exit
      *)
      undirty f.loop_pre_init;
      undirty f.loop_pre_loop;
      let pp = Oct.union f.loop_pre_init.state f.loop_pre_loop.state in
      set f.loop_post_exit (beval pp f.loop_expr_exit);
      if (f.loop_iter < !widen_thres) then
	begin
	  f.loop_iter <- f.loop_iter + 1;
	  set f.loop_post_loop 
	    (beval (Oct.union f.loop_post_loop.state pp) f.loop_expr_loop)
	end	
      else
	begin
	  let v = beval (Oct.widening f.loop_post_loop.state pp 
			   Oct.WidenFast) f.loop_expr_loop in
(*
	  if Oct.is_equal f.loop_post_loop.state v then f.loop_iter <- 0;
*)
	  set f.loop_post_loop v
	end

  in 
  set pre (Oct.universe n);
  try while true do
    match !worklist with 
      []   -> raise Not_found
    | a::l -> 
	worklist:=l;
	if a.dirty then
	  match a.state_post with
	    None -> a.dirty <- false
	  | Some f -> 
	      if !do_debug then Printf.fprintf debug "forward (%i)\n" a.state_id;
	      let (l,_) = location_of_pos a.ctrlpt in
	      if l > !maxl then maxl:=l;
	      eval f
  done with Not_found -> ();
    if !do_debug then Printf.fprintf debug "\n\n"

end
