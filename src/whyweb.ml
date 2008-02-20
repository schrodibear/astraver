
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

open Project

let interp_com c =
  List.iter
    (fun f ->
       if true (* f.function_name = c*) then toggle_function f)
    !proj.project_functions
(*
  let l = List.assoc c !proj.project_lemmas in
  Project.toggle_lemma l
*)

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
	   wprint "</ol>";
	 end
       else
	 begin
	   if !proj.project_name <> script then
	     begin
	       (* TODO: save previous project *)
	       eprintf "Previous project: `%s'@." !proj.project_name;
	       eprintf "Reading file %s.wpr@." script;
	       proj := Project.load (script ^ ".wpr")
	     end
	   else
	     interp_com cont;
	   wprint "<h1 align=center> Project name: %s</h1>" !proj.project_name;
	   
	   wprint "<h2>Lemmas</h2>";
	   wprint "<ol>";
	   List.iter
	     (fun l -> wprint "<li> <a href=\"?%s\">%s</a> </li>" l.lemma_name l.lemma_name)
	     !proj.project_lemmas;
	   wprint "</ol>";
	   
	   wprint "<h2>Functions</h2>";
	   wprint "<ol>";
	   List.iter
	     (fun f -> 
		wprint "<li> <a href=\"?%s\">%s</a> </li>" f.function_name f.function_name;
		if f.function_visible then
		  begin
		    wprint "<ol>";
		    List.iter
		      (fun b -> wprint "<li> %s </li>" b.behavior_name)
		      f.function_behaviors;
		    wprint "</ol>"
		  end)
	     !proj.project_functions;
	   wprint "</ol>";
	 end;
       wprint "</body>")
