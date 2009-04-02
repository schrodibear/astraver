
open Format
open DpConfig

let rc_file () = 
  let home = Rc.get_home_dir () in
  Filename.concat home ".gwhyrc"

(** saving config  *)

let save_main fmt =
  fprintf fmt "[main]@.";
  fprintf fmt "timeout = %d@." (Tools.get_timeout ());
  fprintf fmt "window_width = %d@." !Colors.window_width;
  fprintf fmt "window_height = %d@." !Colors.window_height;
  fprintf fmt "font_size = %d@." !Colors.font_size;
  fprintf fmt "@."

let save_prover_setting fmt (p,s) =
  fprintf fmt "%s = %b@." (Model.prover_id p) s
  
let save_provers fmt l=
  fprintf fmt "[provers]@.";
  List.iter (save_prover_setting fmt) l;
  fprintf fmt "@."

let save () = 
  let ch = open_out (rc_file ()) in
  let fmt = Format.formatter_of_out_channel ch in
  save_main fmt;
  save_provers fmt (Model.get_prover_states ());
  close_out ch



(** loading config *)

let set_main_setting (key,arg) =
  match key with
    | "timeout" -> Tools.set_timeout (Rc.int arg)
    | "window_width" -> Colors.window_width := Rc.int arg
    | "window_height" -> Colors.window_height := Rc.int arg
    | "font_size" -> Colors.font_size := Rc.int arg
    | _ ->
	printf "Unknown field `%s' in section [main] of rc file@." key

let set_prover_setting (key,arg) =
  try
    let b = Rc.bool arg in
    let p = Model.get_prover key in
    if b then Model.select_prover p else Model.deselect_prover p
  with Not_found ->
    printf "Unknown prover id `%s' in section [provers] of rc file@." key
      

let load_default_config () =
  DpConfig.load_rc_file (); (* already done in Stat.main() ? *)
  List.iter
    (fun (pid,(pdata,_)) ->
       if pdata.version <> "" then 
	 try
	   let pr =
	     match pid with
	       | Ergo -> Model.ergo
	       | Simplify -> Model.simplify
	       | Z3 -> Model.z3SS
	       | Cvc3 -> Model.cvc3SS
	       | Yices -> Model.yicesSS
	       | Gappa -> Model.gappa
	       | Coq -> raise Exit (* not yet supported in GWhy *)
	       | Graph|ErgoSelect|Rvsat|Zenon|Cvcl|Harvey ->
		   assert false (* not handled by dpConfig *)
	   in	     
	   printf "installed prover '%s' selected@." pdata.name;
	   Model.select_prover pr
	 with Exit -> ())
    DpConfig.prover_list;
  save ()

  
let load () = 
  let rc_file = rc_file () in
  try
    let rc = Rc.from_file rc_file in
    List.iter
      (fun (key,args) ->
	 match key with
	   | "main" -> List.iter set_main_setting args
	   | "provers" -> List.iter set_prover_setting args
	   | _ -> 
	       printf "Unknown section [%s] in config file '%s'@." key rc_file)
      rc
  with 
    | Not_found -> 
	printf "Config file '%s' does not exists, using default config@." rc_file;
	load_default_config ()
    | Failure msg ->
	printf "Reading '%s' failed (%s), using default config@." rc_file msg;
	load_default_config ()
	

