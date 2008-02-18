
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


let get_name_attr e =
  match List.assoc "name" e.Xml.attributes with
    | Rc.RCstring s -> s
    | _ -> raise Not_found

let get_behavior e =
    match e.Xml.name with
      | "behavior" ->
	  let n = get_name_attr e in
	  (n,()) 
      | _ -> assert false

 
let lemmas = ref []

let functions = ref []

let get_lemma_or_function e =
    match e.Xml.name with
      | "lemma" ->
	  let n = get_name_attr e in
	  lemmas := n :: !lemmas
      | "function" ->
	  let n = get_name_attr e in
	  let behs = List.map get_behavior e.Xml.elements in
	  functions := (n,behs) :: !functions	  
      | _ -> assert false

let project_name = ref ""

(* read XML file *)
let read_file f = 
  let xml = Xml.from_file (f ^ ".wpr") in
  match xml with
    | [p] when p.Xml.name = "project" ->
	project_name := get_name_attr p; 
	if !project_name <> f then
	  eprintf "Warning! project name `%s' does match file name `%s'@." 
	    !project_name f;
	lemmas := [];
	functions := [];
	List.iter get_lemma_or_function p.Xml.elements
    | _ -> failwith "unique <project> element expected"

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
	   if !project_name <> script then
	     begin
	       (* TODO: save previous project *)
	       eprintf "Previous project: `%s'@." !project_name;
	       eprintf "Reading file %s.wpr@." script;
	       read_file script
	     end;
	   wprint "<h1 align=center> Project name: %s</h1>" !project_name;
	   
	   wprint "<h2>Lemmas</h2>";
	   wprint "<ol>";
	   List.iter
	     (fun n -> wprint "<li> <a href=\"?%s\">%s</a> </li>" n n)
	     !lemmas;
	   wprint "</ol>";
	   
	   wprint "<h2>Functions</h2>";
	   wprint "<ol>";
	   List.iter
	     (fun (n,behs) -> 
		wprint "<li> %s </li>" n;
		wprint "<ol>";
		List.iter
		  (fun (n,_) -> wprint "<li> %s </li>" n)
		  behs;
		wprint "</ol>")
	     !functions;
	   wprint "</ol>";
	 end;
       wprint "</body>")
