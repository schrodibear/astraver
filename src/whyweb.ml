open Format
open Project
(* toggle *)

let valid_color = "#00FF00"
let invalid_color = "#FF0033"
let failed_color = "#330000"
let unknown_color = "#FFFF00"
let cannotdecide_color = "#FF00FF"
let running_color = "#0000FF"
let timeout_color = "#990033"

let toggle_lemma l = l.lemma_tags <- 
  List.map (fun (key,value) ->  
	      if key = "ww_open" then 
		if value = "true" then (key,"false") 
		else (key,"true") 
	      else
		(key,value)) l.lemma_tags

let toggle_function f =  f.function_tags <- 
  List.map (fun (key,value) ->  
	      if key = "ww_open" then 
		if value = "true" then (key,"false") 
		else (key,"true") 
	      else
		assert false) f.function_tags

let toggle_behavior b = b.behavior_tags <- 
  List.map (fun (key,value) ->  
	      if key = "ww_open" then 
		if value = "true" then (key,"false") 
		else (key,"true") 
	      else
		(key,value))  b.behavior_tags

let toggle_goal g = g.goal_tags <- 
  List.map (fun (key,value) ->  
	      if key = "ww_open" then 
		if value = "true" then (key,"false") 
		else (key,"true") 
	      else
		(key,value))  g.goal_tags

let use_prover p =
  match p with 
    | "ergo" -> ("--why",".why") 
    | _ -> assert false

open Wserver

let nb_thread = ref 0

let launch_goal  prover context g =  
  let (option,endoffile) = use_prover prover in
  let (reademe,writeme) = Unix.pipe () in
    let _ = Unix.create_process
      "why" [| "why"; "-no-prelude"; option; context; g.goal_file  |]
      Unix.stdin Unix.stdout Unix.stderr in
    let _ = Unix.wait() in
    let _ = Unix.create_process
      "dp" 
      [| "dp"; "-timeout"; "10"; 
	 (String.sub g.goal_file 0 
	    (String.length g.goal_file  - 4))^"_why"^endoffile  |]
      Unix.stdin writeme Unix.stderr in  
    let _ = Unix.wait() in
    let size = 7+(String.length g.goal_file) in
    let buff = String.make 60 '0' in
    let _ = Unix.read reademe buff 0 60 in
    let buff = String.make size '0' in
    let _ = Unix.read reademe buff 0 size in
    eprintf "%s@." buff;
    Unix.close writeme;
    Unix.close reademe;
    let proof = List.filter (fun (s,_) -> s=prover) g.proof in
    (g.proof <-
       match String.get buff ((String.length buff)-1) with 
	 | '.' -> (prover,("valid","10","",""))::proof
	 | '*' -> (prover,("invalid","10","",""))::proof  
	 | '?' -> (prover,("unknown","10","",""))::proof  
	 | '#' -> (prover,("timeout","10","",""))::proof  
	 | '!' -> (prover,("failure","10","",""))::proof 
	 | c -> Format.eprintf "erreur : %c@." c;
	     assert false);
    nb_thread := !nb_thread-1;
    Thread.exit()
   
let version () = 
  printf "This is WhyWeb version %s, compiled on %s
Copyright (c) 2008 - Claude Marché
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
" Version.version Version.date;
  exit 0

let spec =
 [ "-version", Arg.Unit version, 
   "  prints version and exit" ]

let file = ref None

let add_file f = 
  if not (Sys.file_exists f) then begin
    eprintf "whyweb: %s: no such file@." f;
    exit 1
  end;
  file := Some f

let usage = "whyweb [options]"

let () = Arg.parse spec add_file usage

let file = match !file with
  | None -> ()
  | Some f -> Arg.usage spec usage; exit 1

let proj = ref (Project.create "")

let proj_file = ref ""

let coms = Hashtbl.create 1023

let file = ref ""
let line = ref 0
let beginning = ref 0
let ending = ref 0
let current_line = ref 0
let current_page = ref ""


let launch_goal prover g =
  let proof = g.proof in
  g.proof <- (prover,("running","10","",""))::proof;
(*  while !nb_thread > 5 do
    Unix.sleep (10);
  done;    
  nb_thread := !nb_thread+1;*)
  let pid =  Thread.create (launch_goal prover !proj.project_context_file) g in
  Thread.join pid 

let launch_lemmas prover lemmas =
  List.iter (fun l -> launch_goal prover l.lemma_goal) lemmas

let launch_behavior prover b =
  List.iter (launch_goal prover)  b.behavior_goals

let launch_function prover f =
  List.iter (launch_behavior prover) f.function_behaviors

let launch_functions prover functions =
  List.iter (launch_function prover) functions

let interp_com c =
  try
    let (c,loc) = Hashtbl.find coms c in
    begin
    match c with
      | `ToggleFunction f ->()
      | `ToggleLemma l -> ()
      | `ToggleBehavior b -> ()
      | `ToggleGoal g -> ()
      | `OpenFunction f -> toggle_function f
      | `OpenLemma l -> toggle_lemma l
      | `OpenBehavior b -> toggle_behavior b
      | `OpenGoal g -> toggle_goal g
      | `LaunchErgo g -> let _ =  Thread.create (launch_goal "ergo") g in ()
      | `LaunchErgoLemma -> let _ =  
	    Thread.create (launch_lemmas "ergo") !proj.project_lemmas in ()
      | `LaunchErgoFunctions -> let _ =  
	  Thread.create (launch_functions "ergo") !proj.project_functions in ()
      | `LaunchErgoBehavior b -> 
	  let _ =  Thread.create (launch_behavior "ergo")  b in ()
      | `LaunchErgoFunction f -> 
	  let _ =  Thread.create (launch_function "ergo") f  in ()
    end;
    loc
  with Not_found -> ("",0,0,0)

let com_count = ref 0

let reg_com c =
  incr com_count;
  let loc = match c with     
    | `ToggleFunction f ->   
	let (_,lin,_,_) = f.function_loc in
	current_line := lin; 
	f.function_loc
    | `ToggleLemma l -> 
	let (_,lin,_,_) = l.lemma_loc in
	current_line := lin;
	l.lemma_loc
    | `ToggleBehavior b -> 
	let (_,lin,_,_) = b.behavior_loc in
	current_line := lin;
	b.behavior_loc
    | `ToggleGoal g -> 
	let (_,lin,_,_) = g.goal_expl.Logic_decl.vc_loc in
	current_line := lin;
	g.goal_expl.Logic_decl.vc_loc   
    | `OpenFunction _
    | `OpenLemma _
    | `OpenBehavior _
    | `OpenGoal _ -> (!file,!line,!beginning,!ending)
    | `LaunchErgo _ -> (!file,!line,!beginning,!ending) 
    | `LaunchErgoLemma -> (!file,!line,!beginning,!ending)
    | `LaunchErgoFunctions -> (!file,!line,!beginning,!ending)
    | `LaunchErgoBehavior  _ -> (!file,!line,!beginning,!ending)
    | `LaunchErgoFunction  _ -> (!file,!line,!beginning,!ending)
  in
  let n = string_of_int !com_count in
  Hashtbl.add coms n (c,loc);
  !proj.project_name ^ "?" ^ n
  

(* main *)

open Wserver
open Format

let main_page msg =
  wprint "<h1 align=center>Welcome to the World-Why-Web</h1><hr>";
  wprint "<h2>List of current projects</h2>";
  wprint "<ol>";
  wprint "<li> <a href=\"?test\">test</a>";
  wprint "<li> <a href=\"?bench/java/good/why/Gcd.wpr\">Gcd</a>";
  wprint "<li> <a href=\"?bench/java/good/why/Lesson1.wpr\">Lesson1</a>";
  wprint "</ol>";
  if msg <> "" then
    begin
      wprint "<hr>%s" msg;
    end

let load_prj file =
  eprintf "Reading file %s@." file;
  try
    proj := Project.load file;
    proj_file := file;
  with
      Sys_error _ -> 
	let msg = "Cannot open file " ^ file in
	eprintf "%s@." msg;
	main_page msg;
	raise Exit
	
let toogletooltip b s =
  (if b then "close" else "open") ^ s
  
let rec find_prover l = 
  match  l with
    | (prover,(status,_,_,_))::l -> (prover,status)::(find_prover l)
    | [] -> []

let validity nl valid = 
  let(valid,color) =
    match valid with 
    | "valid" -> "Valid", valid_color
    | "timeout" -> "TimeOut", timeout_color
    | "cannotdecide" -> "CannotDecide", cannotdecide_color
    | "invalid" ->  "Invalid", invalid_color
    | "failure"-> "Failed", failed_color
    | "running" -> "Running", running_color
    | _ -> assert false 
  in
  wprint "</td><td bgcolor=\"%s\"><a href=\"%s\">%s</a></td></tr>" 
   color nl valid

let goal_validity prover g nl =   
  let list_prover = find_prover g.proof in
  let valid =  try 
      List.assoc prover list_prover 
    with Not_found -> "invalid" 
  in 
  validity nl valid

let goal_is_valid prover g = 
  let (v,_,_,_) = try List.assoc prover g.proof  
    with Not_found -> ("invalid","","","")
  in
  v = "valid"

let behavior_validity prover b =
  List.for_all (goal_is_valid prover)  b.behavior_goals 

let function_validity prover f =
  List.for_all (behavior_validity prover) f.function_behaviors

let goal g indice indent =
  let s =fprintf str_formatter "%s" 
    (Explain.msg_of_kind g.goal_expl.Logic_decl.vc_kind);
    flush_str_formatter ()
  in
  let nt = reg_com (`ToggleGoal g) in 
  let no = reg_com (`OpenGoal g) in 
  let nl = reg_com (`LaunchErgo g) in 
  let op = List.assoc "ww_open" g.goal_tags = "true" in
  if op 
  then wprint "<tr><td>&nbsp &nbsp %s<a href=\"%s#%d\">-</a>" indent no !current_line
  else wprint "<tr><td>&nbsp &nbsp %s<a href=\"%s#%d\">+</a>" indent no !current_line; 
  wprint "%d : <a href=\"%s#%d\">%s</a>
" indice nt !current_line s;
  if op 
  then
    begin
      try
	wprint "<pre>";
	let fi = open_in g.goal_file in
	begin
	  try 
	    while true do  
	      wprint "%s
" (input_line fi);
	    done
	  with End_of_file -> close_in fi
	end;
	wprint "</pre>";
      with Sys_error _ -> 
	wprint "File %s don't exist" g.goal_file;
    end;
  goal_validity "ergo" g nl

let string_of_addr addr = 
  match addr with 
    | Unix.ADDR_UNIX s -> s
    | Unix.ADDR_INET (ie,i) -> 
	(Unix.string_of_inet_addr ie)^":"^string_of_int(i)

let () =
  Wserver.f None 2372 60 None
    (fun (addr,req) script cont ->
       eprintf "add : %s@." (string_of_addr addr);
       eprintf "request: %a@." (Pp.print_list Pp.comma pp_print_string) req;
       eprintf "script: `%s'@." script;
       eprintf "cont: `%s'@." cont;
       http "";
       current_page := "http://localhost:2372/" ^ script;
       wprint "
<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">
<html>
<head>
<META HTTP-EQUIV=\"Refresh\" CONTENT=\"10; URL=%s\"> 
<meta http-equiv=\"Content-Type\" content=\"text/html; charset=iso-8859-1\">
<title> 
WhyWeb
</title><style type=\"text/css\">
.lemenu {
  position: absolute;
  top: 4em;
  overflow: auto; 
  width: 50%%;
  height: 93%%;
}

h1 {   
  height: 5%%;
}

.content {
  margin:0em 0px 0em 50%%;
  overflow: auto; 
  height: 93%%;
}
</style>
</head>
<body>" !current_page;
       try
	 if script = "" then 
	   begin
	     if cont = "" then (main_page ""; raise Exit);
	     load_prj cont;
	   end
	 else 
	   if !proj.project_name <> script then
	     begin
	       eprintf "Previous project: `%s'@." !proj.project_name;
	       eprintf "TODO: save previous project@.";
	       main_page "Argument is not the currently opened project";
	       raise Exit
	     end;
	 let (loc_file,loc_line,loc_beginning,loc_ending) = interp_com cont in
	 file := loc_file;
	 line := loc_line;
	 beginning := loc_beginning;
	 ending := loc_ending;
	 Hashtbl.clear coms;
	 com_count := 0;
	 wprint "<h1 align=center> Project name: %s</h1>

<div class=\"lemenu\">
<table border=\"1\"  cellpadding=\"0\" cellspacing=\"0\">" !proj.project_name;
	 wprint "<tr><th></th><th>Alt-Ergo</th></tr>
";
	 wprint "<tr><th>Lemmas</th>"; 
	 let nl = reg_com (`LaunchErgoLemma) in 
	 if (List.for_all (fun l -> 
			     List.for_all 
			       (fun pr ->
				  let (_,(status,_,_,_)) = pr  in 
				  status = "valid") l.lemma_goal.proof) 
	       !proj.project_lemmas) 
	 then validity nl "valid"
	 else validity nl "invalid" 
	 ;
	 let indice = ref 1 in
	 List.iter
	   (fun l -> 
	      let nt = reg_com (`ToggleLemma l) in 
	      let no = reg_com (`OpenLemma l) in 
	      let op = List.assoc "ww_open" l.lemma_tags = "true" in
	      if op 
	      then wprint "<tr><td><a href=\"%s#%d\">-</a>" no !current_line
	      else wprint "<tr><td><a href=\"%s#%d\">+</a>" no !current_line;
	      wprint "%d : <a href=\"%s#%d\">%s</a></td>" !indice nt 
		!current_line l.lemma_name;
	      wprint "<td>Ergo</td></tr>
";
	      indice := !indice +1;
	      if op then 
		begin 
		  goal l.lemma_goal 1 ""; 
		end 
	   )
	   !proj.project_lemmas;
	 wprint "<tr><td></td><td></td></tr>
";
	 wprint "<tr><th>Functions</th>
";
	 let nl = reg_com (`LaunchErgoFunctions) in 
	 if (List.for_all (function_validity "ergo") !proj.project_functions) 
	 then validity nl "valid" 
	 else validity nl "invalid"
	 ;
	 let indice = ref 1 in
	 List.iter
	   (fun f -> 
	      let nt = reg_com (`ToggleFunction f) in 
	      let no = reg_com (`OpenFunction f) in 
	      let nl = reg_com (`LaunchErgoFunction f) in
	      let op = List.assoc "ww_open" f.function_tags = "true" in
	      if op
	      then wprint "<tr><td><a href=\"%s#%d\">-</a>" no !current_line
	      else wprint "<tr><td><a href=\"%s#%d\">+</a>" no !current_line;
	      wprint "%d : <a href=\"%s#%d\">%s</a></td>
" !indice nt !current_line f.function_name;
	      if (function_validity "ergo" f)
	      then validity nl "valid"
	      else validity nl "invalid"
		;
	      indice := !indice +1;
	      if op then
		begin
		  let indice = ref 1 in
		  List.iter
		    (fun b ->
		       let nt = reg_com (`ToggleBehavior b) in 
		       let no = reg_com (`OpenBehavior b) in 
		       let nl = reg_com (`LaunchErgoBehavior b) in
		       let op = 
			 List.assoc "ww_open" b.behavior_tags = "true" in
		       if op 
		       then 
			 wprint "<tr><td>&nbsp &nbsp<a href=\"%s#%d\">-</a>" no !current_line
		       else 
			 wprint "<tr><td>&nbsp &nbsp<a href=\"%s#%d\">+</a>" no !current_line;
		       wprint "%d : <a href=\"%s#%d\">%s</a></td>>
" !indice nt !current_line b.behavior_name;
		       if (behavior_validity "ergo" b)
		       then validity nl "valid"
		       else validity nl "invalid"
		       ;
		       indice := !indice +1;
		       if op then
			 begin
			   let indice = ref 0 in
			   List.iter(fun x ->   indice :=  !indice +1;goal x !indice "&nbsp &nbsp") b.behavior_goals;
			 end)
		    f.function_behaviors;
		end)
	   !proj.project_functions;
	 raise Exit
       with
	   Exit -> 
	     begin
	       wprint "
</table>
</div>

<div class=\"content\"> <pre>
";
	       if !file = "" then ()
	       else 
		 let fi = open_in !file in
		 begin
		   try 
		     let l = ref 1 in
		     let c = ref 1 in
		     let in_select = ref false in
		     wprint "<a name=\"%d\"></a>" !l;
		     while true do  
		       let char = input_char fi in
		       if char = '\n'
		       then
			 begin
			   l := !l+1;
			   if not !in_select then c := 0 else ();
			   wprint "<a name=\"%d\"></a>" !l
			 end
		       else ();
		       if (!l = !line && !c = !beginning)
		       then
			 begin
			   wprint "<FONT style=\"BACKGROUND-COLOR: #FFCC99\">";
			   in_select := true
			 end
		       else ();
		       wprint "%c" char;
		       if (!c = !ending) then wprint "</font>" else ();
		       c := !c+1
		     done
		   with End_of_file -> close_in fi
		 end;
		 wprint "</pre></div>
</body>
</html>"
	     end)
