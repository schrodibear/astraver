
open Format
open DpConfig

let rec detect_prover p cmds =
  match cmds with
    | [] ->
	printf "detection of prover %s failed@." p.name
    | cmd::rem ->
	let out = Filename.temp_file "out" "" in
	let c = cmd ^ " " ^ p.version_switch ^ " > " ^ out in
(*
	eprintf "debug: command = %s@." c;
*)
	let ret = Sys.command c in
	if ret <> 0 then
	  begin
	    printf "command %s failed@." cmd;
	    detect_prover p rem
	  end
	else
	  let ch = open_in out in
	  let s = input_line ch in
	  let re = Str.regexp p.version_regexp in
	  if Str.string_match re s 0 then
	    let nam = p.name in
	    let ver = Str.matched_group 1 s in
	    printf "Found prover %s version %s@." nam ver;
	    p.command <- cmd;
	    p.version <- ver;
	  else
	    begin
	      printf "Warning: found prover %s but name/version not recognized by regexp `%s'@." p.name p.version_regexp;
	      printf "Answer was `%s'@." s;
	      p.command <- cmd;
	      p.version <- "";
	    end
		
	
let main () =
  begin
    try
      load_rc_file ()
    with Not_found -> 
      printf "rc file not found, using default values for provers@\n@.";
  end;
  printf "starting autodetection...@.";
  List.iter (fun (p,l) -> detect_prover p (l@[p.command])) prover_list;
  printf "detection done.@.";
  printf "writing rc file...@.";
  save_rc_file ()


let () = Printexc.catch main ()

  
  

