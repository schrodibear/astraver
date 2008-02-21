
open Format

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

open Project

let coms = Hashtbl.create 1023

let interp_com c =
  try
    let c = Hashtbl.find coms c in
    match c with
      | `ToggleFunction f -> toggle_function f
      | `ToggleLemma l -> toggle_lemma l
      | `ToggleBehavior b -> toggle_behavior b
  with Not_found -> ()

let com_count = ref 0

let reg_com c =
  incr com_count;
  let n = string_of_int !com_count in
  Hashtbl.add coms n c;
  n
  

(* main *)

open Wserver
open Format

let () =
  Wserver.f None 2372 60 None
    (fun (addr,req) script cont ->
(*
       eprintf "request: %a@." (Pp.print_list Pp.comma pp_print_string) req;
*)
       eprintf "script: `%s'@." script;
       eprintf "cont: `%s'@." cont;
       http ""; 
       wprint "
<html><head>
<META http-equiv=\"Content-Type\" content=\"text/html; charset=utf8\">
</head><body>";
       if script = "" then
	 begin
	   wprint "<h1 align=center>Welcome to the World-Why-Web</h1><hr>";
	   wprint "<h2>List of current projects</h2>";
	   wprint "<ol>";
	   wprint "<li> <a href=\"test\">test</a>";
	   wprint "<li> <a href=\"Gcd\">Gcd</a>";
	   wprint "<li> <a href=\"Lesson1\">Lesson1</a>";
	   wprint "</ol>";
	 end
       else
	 begin
	   if !proj_file <> script then
	     begin
	       (* TODO: save previous project *)
	       eprintf "Previous project: `%s'@." !proj.project_name;
	       eprintf "Reading file %s.wpr@." script;
	       proj_file := script;
	       proj := Project.load (script ^ ".wpr")
	     end
	   else
	     interp_com cont;
	   Hashtbl.clear coms;
	   com_count := 0;
	   wprint "<h1 align=center> Project name: %s</h1>" !proj.project_name;
	   
	   wprint "<h2>Lemmas</h2>";
	   wprint "<ol>";
	   List.iter
	     (fun l -> 
		let n = reg_com (`ToggleLemma l) in 
		wprint "<li> <a href=\"?%s\">%s</a> </li>" n l.lemma_name)
	     !proj.project_lemmas;
	   wprint "</ol>";
	   
	   wprint "<h2>Functions</h2>";
	   wprint "<ol>";
	   List.iter
	     (fun f -> 
		let n = reg_com (`ToggleFunction f) in 
		wprint "<li> <a href=\"?%s\">%s</a> </li>" n f.function_name;
		if f.function_open then
		  begin
		    wprint "<ol>";
		    List.iter
		      (fun b ->
			 let n = reg_com (`ToggleBehavior b) in 
			 wprint "<li> <a href=\"?%s\">%s</a> </li>" n b.behavior_name;
			 if b.behavior_open then
			   begin
			     wprint "<ol>";
			     List.iter
			       (fun g ->
				  let s =
				    fprintf str_formatter "%a" Explain.print g.goal_expl;
				    flush_str_formatter ()
				  in
				  wprint "<li> %s </li>" s)
			       b.behavior_goals;
			     wprint "</ol>"
			   end)
		      f.function_behaviors;
		    wprint "</ol>"
		  end)
	     !proj.project_functions;
	   wprint "</ol>";
	 end;
       wprint "</body>")
