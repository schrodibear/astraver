open Cast

let rec expr e =
  match e.texpr_node with 
    | TEnop -> []
    | TEconstant _ -> []
    | TEstring_literal _ -> []
    | TEvar (Info.Fun_info f ) -> [f]    
    | TEvar (Info.Var_info f ) -> []
    | TEdot (e, _) -> expr e
    | TEarrow (e, _) -> expr e
    | TEarrget (e1, e2) -> (expr e1)@(expr e2)
    | TEseq (e1, e2) -> (expr e1)@(expr e2)
    | TEassign (e1, e2) -> (expr e1)@(expr e2)
    | TEassign_op(e1, _, e2) -> (expr e1)@(expr e2)
    | TEunary (_, e) -> expr e
    | TEincr (_, e) -> expr e
    | TEbinary (e1, _, e2) -> (expr e1)@(expr e2)
    | TEcall (e, le) -> (expr e)@
	(List.fold_left (fun acc x -> (expr x)@acc) [] le)
    | TEcond (e1, e2 ,e3) -> (expr e1)@(expr e2)@(expr e3)
    | TEcast (_, e) | TEmalloc (_, e) -> expr e
    | TEsizeof _ -> []

let rec statement s = 
  match s.st_node with  
    | TSnop -> []
    | TSexpr e -> expr e
    | TSif (e, s1, s2) -> (expr e)@(statement s1)@(statement s2)  
    | TSwhile (_,e,s) -> (expr e)@(statement s)
    | TSdowhile (_,s,e) -> (statement s)@(expr e)
    | TSfor (_, e1, e2, e3, s) -> (expr e1)@(expr e2)@(expr e3)@(statement s)
    | TSblock (_, sl) -> List.fold_left (fun acc x -> (statement x)@acc) [] sl 
    | TSreturn _ -> []
    | TSbreak -> []
    | TScontinue -> []
    | TSlabel (_, s) -> statement s
    | TSswitch (e, s) -> (expr e)@(statement s)
    | TScase  (e, s) -> (expr e)@(statement s)
    | TSdefault s -> statement s
    | TSgoto _ -> []
    | TSassert _ -> []
    | TSlogic_label _ -> []
    | TSspec (_, s) -> statement s
    | TSset _ -> [] 

let make_graph e = 
  match e with    
  | Tfundef (s, t, f, st) -> f.Info.graph <- statement st 
  | _ -> ()

      
let file =  List.iter (fun d -> make_graph d.node)
