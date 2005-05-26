open Info

let print_graph () = 
  Cenv.iter_sym 
    (fun n x -> match x with
       | Var_info _ -> () 
       | Fun_info f -> 
	   Format.eprintf "%s :"  f.fun_name;
	   List.iter (fun x -> Format.eprintf " %s," x.fun_name) f.graph;
	   Format.eprintf "@\n")
