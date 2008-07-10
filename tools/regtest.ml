(** the options to launch the toplevel with if the test file is not
     annotated with test options *)
let default_options = [ "" ]

(** the list of tests suites to consider *)
let default_suites =
[ "java" ]

let () =
  Unix.putenv "FRAMAC_SHARE" (Filename.concat Filename.current_dir_name "share");
  Unix.putenv "OCAMLRUNPARAM" ""

(** the name of the directory-wide configuration file*)
let dir_config_file = "test_config"

(** the files in [suites] whose name matches
    the pattern [test_file_regexp] will be considered as test files *)
let test_file_regexp = ".*\\.\\(java\\)$"

(** the pattern that ends the parsing of options in a test file *)
let end_comment = Str.regexp ".*\\*/"

let opt_to_byte =
  let opt = Str.regexp "[.]opt$" in
  function toplevel ->
    Str.global_replace opt ".byte" toplevel

let base_path = Filename.current_dir_name
(*    (Filename.concat
        (Filename.dirname Sys.executable_name)
	Filename.parent_dir_name)
*)

let test_path = "tests"

(** Command-line flags *)

type behavior = Examine | Update | Run | Show
let behavior = ref Run
let verbosity = ref 0
let use_byte = ref false
let do_diffs = ref "diff -u"
let n = ref 4    (* the level of parallelism *)
let suites = ref []
(** options given to toplevel for all tests *)
let additional_options = ref ""
(** special configuration, with associated oracles *)
let special_config = ref ""

let m = Mutex.create ()

let lock_fprintf f =
  Mutex.lock m;
  Format.kfprintf (fun _ -> Mutex.unlock m) f

let lock_printf s = lock_fprintf Format.std_formatter s
let lock_eprintf s = lock_fprintf Format.err_formatter s

let make_test_suite s =
  suites := s :: !suites

let () = Arg.parse
  [
    "", Arg.Unit (fun () -> ()) , "" ;
    "-examine", Arg.Unit (fun () -> behavior := Examine) ,
    " Examine the logs that are different from oracles.";
    "-update", Arg.Unit (fun () -> behavior := Update) ,
    " Take the current logs as oracles.";
    "-show", Arg.Unit (fun () -> behavior := Show; use_byte := true) ,
    " Show the results of the tests. Sets -byte.";
    "-run", Arg.Unit (fun () -> behavior := Run) ,
    "(default)  Delete the logs, run the tests, then examine the logs that are different from the oracles.";
    "", Arg.Unit (fun () -> ()) , "" ;
    "-v", Arg.Unit (fun () -> incr verbosity), " Increase verbosity (up to twice)" ;
    "-diff", Arg.String (fun s -> do_diffs := s), "<command>  Use command for diffs" ;
    "-j", Arg.Int (fun i -> if i>=0 then n := i else ( lock_printf "Option -j requires nonnegative argument@."; exit (-1))), "<n>  Use nonnegative integer n for level of parallelism" ;
    "-byte", Arg.Set use_byte, " Use bytecode toplevel";
    "-opt", Arg.Clear use_byte, " Use native toplevel (default)";
    "-config", Arg.Set_string special_config, " Use special configuration \
      and oracles";
    "-add-options", Arg.Set_string additional_options,
    "add additional options to be passed to the toplevels \
     that will be launched";
    "", Arg.Unit (fun () -> ()) ,"\nA test suite can be the name of a directory in ./tests or the path to a file.\n\nExamples:\nregtest\nregtest -diff \"echo diff\" -examine     # see again the list of tests that failed\nregtest misc                           # for a single test suite\nregtest tests/misc/alias.c             # for a single test\nregtest -examine tests/misc/alias.c    # to see the differences again\nregtest -v -j 1                        # to check the time taken by each test\n"
  ]
  make_test_suite
  "usage: ./regtest.opt [options] [names of test suites]"

(* redefine config file if special configuration expected *)
let dir_config_file = 
  if !special_config = "" then dir_config_file else
    dir_config_file ^ "_" ^ !special_config

let make_toplevel_path exec = exec
(*  if Filename.is_relative exec then
    Filename.concat (Filename.concat base_path "bin") exec
  else exec
*)

(* redefine oracle directory if special configuration expected *)
let oracle_dirname = 
  if !special_config = "" then "oracle" else
    "oracle_" ^ !special_config
 
(* redefine result directory if special configuration expected *)
let result_dirname = 
  if !special_config = "" then "result" else
    "result_" ^ !special_config

let gen_make_file s dir file = Filename.concat (Filename.concat dir s) file
let make_result_file = gen_make_file result_dirname
let make_oracle_file = gen_make_file oracle_dirname

let toplevel_path =
  make_toplevel_path (gen_make_file "tests" base_path "regtest.sh")

type execnow =
    {
      ex_cmd: string;      (** command to launch *)
      ex_log: string list; (** log files *)
      ex_bin: string list; (** bin files *)
      ex_dir: string;      (** directory of test suite *)
    }

(** configuration of a directory/test. *)
type config =
    {
      dc_test_regexp: string; (** regexp of test files. *)
      dc_execnow    : execnow option; (** command to be launched before
                                         the toplevel(s)
                                     *)
      dc_toplevel   : string; (** full path of the toplevel used *)
      dc_filter     : string option; (** optional filter to apply to
			      standard output *)
      dc_options    : string list; (** options to launch the toplevel on *)
      dc_dont_run   : bool;
    }

let default_config =
  { dc_test_regexp = test_file_regexp ;
    dc_execnow = None;
    dc_toplevel = toplevel_path ;
    dc_filter = None ;
    dc_options = default_options ;
    dc_dont_run = false;
  }

let launch command_string =
  let result = Unix.system command_string in
  match result with
  | Unix.WEXITED 127 ->
      lock_printf "%% Couldn't execute command `%s'@.Retrying once.@." command_string;
      Thread.delay 0.1;
      ( match Unix.system command_string with
	Unix.WEXITED r when r <> 127 -> r
      | _ -> lock_printf "%% Retry failed, exiting.@."; exit 1 )
  | Unix.WEXITED r -> r
  | Unix.WSIGNALED s ->
      lock_printf "%% SIGNAL %d received while executing command:@\n%s@\nStopping@."
	s command_string ;
      exit 1
  | Unix.WSTOPPED s ->
      lock_printf "%% STOP %d received while executing command:@\n%s@\nStopping@."
	s command_string;
      exit 1

let scan_execnow dir (s:string) =
  let rec aux (s:execnow) =
    try
      Scanf.sscanf s.ex_cmd "%[ ]LOG %[A-Za-z0-9_',+=:.] %s@\n"
	(fun _ name cmd ->
	   aux { s with ex_cmd = cmd; ex_log = name :: s.ex_log })
    with Scanf.Scan_failure _ ->
      try
	Scanf.sscanf s.ex_cmd "%[ ]BIN %[A-Za-z0-9.] %s@\n"
	  (fun _ name cmd ->
	     aux { s with ex_cmd = cmd; ex_bin = name :: s.ex_bin })
      with Scanf.Scan_failure _ ->
	s
  in
  aux { ex_cmd = s; ex_log = []; ex_bin = []; ex_dir = dir }

(* how to process options *)
let config_options =
  [ "CMD",
    (fun _ s (current,rev_opts) ->
       { current with dc_toplevel = make_toplevel_path s}, rev_opts);

    "OPT",
    (fun _ s (current,rev_opts) -> current, (s::rev_opts) );

    "FILEREG",
    (fun _ s (current,rev_opts) ->
       { current with dc_test_regexp = s }, rev_opts );

    "FILTER",
    (fun _ s (current,rev_opts) ->
       { current with dc_filter = Some s }, rev_opts );

    "GCC",
    (fun _ _ acc -> acc);

    "COMMENT",
    (fun _ _ acc -> acc);

    "DONTRUN",
    (fun _ s (current,rev_opts) ->
       { current with dc_dont_run = true }, rev_opts );

    "EXECNOW",
    (fun dir s (current,rev_opts)->
       let execnow = scan_execnow dir s in
       { current with dc_execnow = Some execnow }, rev_opts);
  ]

let scan_options dir scan_buffer default =
  let r = ref (default, [])  in
  let treat_line s =
    try
      Scanf.sscanf s "%[ *]%[A-Za-z0-9]:%s@\n"
        (fun _ name opt ->
          try
            r := (List.assoc name config_options) dir opt !r
          with Not_found ->
            lock_eprintf "@[unknown configuration option: %s@\n%!@]" name)
    with Scanf.Scan_failure _ ->
      if Str.string_match end_comment s 0
      then raise End_of_file
      else ()
  in
  try
    while true do
      Scanf.bscanf scan_buffer "%s@\n" treat_line
    done;
    assert false
  with
    End_of_file ->
      let rev_options = snd !r in
      let options =
	if rev_options = []
	then default.dc_options
	else List.rev rev_options
      in
      { (fst !r) with dc_options = options }

let scan_test_file default dir f =
  let f = Filename.concat dir f in
  let exists_as_file =
    try
      (Unix.lstat f).Unix.st_kind = Unix.S_REG
    with Unix.Unix_error _ | Sys_error _ -> false
  in
    if exists_as_file then begin
        let scan_buffer = Scanf.Scanning.from_file f in
          try
            Scanf.bscanf scan_buffer "/* run.config%s@\n" (fun _ -> ());
            scan_options dir scan_buffer default
          with
            | End_of_file
            | Scanf.Scan_failure _ ->
                default
      end else
      (* if the file has disappeared, don't try to run it... *)
      { default with dc_dont_run = true }

type toplevel_command =
    { file : string ;
      options : string ;
      toplevel: string ;
      filter : string option ;
      directory : string ;
      n : int }

type command =
  | Toplevel of toplevel_command
  | Target of execnow * command Queue.t

type log = Err | Res

type diff =
  | Command_error of toplevel_command * log
  | Target_error of execnow
  | Log_error of string (** directory *) * string (** file *)

type cmps =
  | Cmp_Toplevel of toplevel_command
  | Cmp_Log of string (** directory *) * string (** file *)

type shared =
    { lock : Mutex.t ;
      lock_target : Mutex.t ;
      commands_empty : Condition.t ;
      work_available : Condition.t ;
      diff_available : Condition.t ;
      mutable commands : command Queue.t ; (* file, options, number *)
      cmps : cmps Queue.t ;
      (* command that has finished its execution *)
      diffs : diff Queue.t ;
      (* cmp that showed some difference *)
      mutable commands_finished : bool ;
      mutable cmp_finished : bool ;
      mutable summary_run : int ;
      mutable summary_ok : int ;
      mutable summary_log : int;
    }

let shared =
  { lock = Mutex.create () ;
    lock_target = Mutex.create () ;
    commands_empty = Condition.create () ;
    work_available = Condition.create () ;
    diff_available = Condition.create () ;
    commands = Queue.create () ;
    cmps = Queue.create () ;
    diffs = Queue.create () ;
    commands_finished = false ;
    cmp_finished = false ;
    summary_run = 0 ;
    summary_ok = 0 ;
    summary_log = 0 }

let unlock () = Mutex.unlock shared.lock

let lock () = Mutex.lock shared.lock

let catenate_number prefix n =
  if n > 0
  then prefix ^ "." ^ (string_of_int n)
  else prefix

let name_without_extension command =
  try
    (Filename.chop_extension command.file)
  with
    Invalid_argument _ ->
      failwith ("Ce nom de fichier de test ne comporte pas d'extension: " ^
		   command.file)

let gen_prefix s cmd =
  let prefix = gen_make_file s cmd.directory (name_without_extension cmd) in
  catenate_number prefix cmd.n

let log_prefix = gen_prefix result_dirname
let oracle_prefix = gen_prefix oracle_dirname

let basic_command_string command =
  command.toplevel ^ " " ^
    command.options ^ " " ^
    !additional_options ^ " " ^
    (Filename.concat command.directory command.file)

let command_string command =
  let log_prefix = log_prefix command in
  let command_string = basic_command_string command in
  let command_string =
    command_string ^ " 2>" ^ log_prefix ^ ".err.log"
  in
  let command_string =
    match command.filter with
      None -> command_string
    | Some filter ->
	command_string ^ " | " ^ filter
  in
  let command_string =
    command_string ^ " >" ^ log_prefix ^ ".res.log"
  in
  command_string

let update_toplevel_command command =
  let log_prefix = log_prefix command in
  let oracle_prefix = oracle_prefix command in
  let command_string =
    "mv " ^
      log_prefix ^ ".res.log " ^
      oracle_prefix ^ ".res.oracle"
  in
  ignore (launch command_string);
 let command_string =
    "mv " ^
      log_prefix ^ ".err.log " ^
      oracle_prefix ^ ".err.oracle"
  in
  ignore (launch command_string)

let update_command = function
    Toplevel cmd -> update_toplevel_command cmd
  | Target _ -> assert false

let update_log_files dir file =
  let command_string =
    "mv " ^ make_result_file dir file ^ " " ^ make_oracle_file dir file
  in
  ignore (launch command_string)

let do_command command =
  match command with
    Toplevel command ->
      (* Update : copy the logs. Do not enqueue any cmp
         Run | Show: launch the command, then enqueue the cmp
         Examine : just enqueue the cmp *)
      if !behavior = Update
      then update_toplevel_command command
      else begin
          (* Run, Show or Examine *)
          if !behavior <> Examine
          then begin
	      let command_string = command_string command in
	      if !verbosity >= 1
	      then lock_printf "%s@." command_string ;
	      ignore (launch command_string)
	    end;
	  lock ();
	  shared.summary_run <- succ shared.summary_run ;
	  shared.summary_log <- shared.summary_log + 2 ;
	  Queue.push (Cmp_Toplevel command) shared.cmps;
	  unlock ()
	end
  | Target (execnow, cmds) ->
      if !behavior = Update then begin
	  List.iter (update_log_files execnow.ex_dir) execnow.ex_log;
          Queue.iter update_command cmds
	end else
        begin
          let res =
            if !behavior <> Examine then begin
		let filenames =
		  List.fold_left
		    (fun s f -> s ^ " " ^ make_result_file execnow.ex_dir f)
		    ""
		    (execnow.ex_bin @ execnow.ex_log)
		in
		(* TODO this should be done with Unix.unlink *)
		ignore (launch ("rm" ^ filenames ^ " 2> /dev/null"));
		Mutex.lock shared.lock_target;
		let r = launch execnow.ex_cmd in
		Mutex.unlock shared.lock_target;
		r
              end else
	      0
          in
          lock();
	  shared.summary_log <- succ shared.summary_log;
          if res = 0
	  then begin
	      shared.summary_ok <- succ shared.summary_ok;
              Queue.transfer shared.commands cmds;
	      shared.commands <- cmds;
              Condition.signal shared.work_available;
	      if !behavior = Examine || !behavior = Run
	      then begin
		  List.iter
		    (fun f -> Queue.push (Cmp_Log(execnow.ex_dir, f)) shared.cmps)
		    execnow.ex_log
		end
            end
	  else begin
	      let treat_cmd = function
		  Toplevel cmd ->
		    shared.summary_run <- shared.summary_run + 1;
		    let log_prefix = log_prefix cmd in
		    begin try
			Unix.unlink (log_prefix ^ ".res.log ")
		      with Unix.Unix_error _ -> ()
		    end;
		| Target _ -> assert false
	      in
	      Queue.iter treat_cmd cmds;
              Queue.push (Target_error execnow) shared.diffs;
              Condition.signal shared.diff_available
            end;
          unlock()
        end

let log_ext = function Res -> ".res" | Err -> ".err"

let compare_one_file cmp log_prefix oracle_prefix log_kind =
  if !behavior = Show
  then begin
    lock();
    Queue.push (Command_error(cmp,log_kind)) shared.diffs;
    Condition.signal shared.diff_available;
    unlock()
  end else
    let ext = log_ext log_kind in
    let log_file = log_prefix ^ ext ^ ".log " in
    let oracle_file = oracle_prefix ^ ext ^ ".oracle" in
    let cmp_string = "cmp -s " ^ log_file ^ oracle_file in
    if !verbosity >= 2 then lock_printf "%% cmp%s (%d) :%s@."
      ext
      cmp.n
      cmp_string;
    match launch cmp_string with
      0 ->
	lock();
	shared.summary_ok <- shared.summary_ok + 1;
	unlock()
    | 1 ->
	lock();
	Queue.push (Command_error (cmp,log_kind)) shared.diffs;
	Condition.signal shared.diff_available;
	unlock()
    | 2 ->
	lock_printf
	  "%% System error while comparing. Maybe one of the files is missing...@\n%s or %s@."
	  log_file oracle_file;
    | _ -> assert false

let compare_one_log_file dir file =
  if !behavior = Show
  then begin
    lock();
    Queue.push (Log_error(dir,file)) shared.diffs;
    Condition.signal shared.diff_available;
    unlock()
  end else
    let log_file = make_result_file dir file in
    let oracle_file = make_oracle_file dir file in
    let cmp_string = "cmp -s " ^ log_file ^ " " ^ oracle_file in
    if !verbosity >= 2 then lock_printf "%% cmplog: %s / %s@." dir file;
    shared.summary_log <- succ shared.summary_log;
    match launch cmp_string with
      0 ->
	lock();
	shared.summary_ok <- shared.summary_ok + 1;
	unlock()
    | 1 ->
	lock();
	Queue.push (Log_error (dir,file)) shared.diffs;
	Condition.signal shared.diff_available;
	unlock()
    | 2 ->
	lock_printf
	  "%% System error while comparing. Maybe one of the files is missing...@\n%s or %s@."
	  log_file oracle_file;
    | _ -> assert false

let do_cmp = function
  | Cmp_Toplevel cmp ->
      let log_prefix = log_prefix cmp in
      let oracle_prefix = oracle_prefix cmp in
      compare_one_file cmp log_prefix oracle_prefix Res;
      compare_one_file cmp log_prefix oracle_prefix Err
  | Cmp_Log(dir, f) ->
      compare_one_log_file dir f

let worker_thread () =
  while true do
    lock () ;
    if (Queue.length shared.commands) + (Queue.length shared.cmps) < !n
    then Condition.signal shared.commands_empty;
    try
      let cmp = Queue.pop shared.cmps in
      unlock () ;
      do_cmp cmp
    with Queue.Empty ->
      try
	let command = Queue.pop shared.commands in
	unlock () ;
	do_command command
      with Queue.Empty ->
	if shared.commands_finished then (unlock () ; Thread.exit ());

	Condition.signal shared.commands_empty;
	(* we still have the lock at this point *)

	Condition.wait shared.work_available shared.lock;
	  (* this atomically releases the lock and suspends
	     the thread on the condition work_available *)

	unlock ();
  done

let do_diff = function
  | Command_error (diff, kind) ->
      let log_prefix = log_prefix diff in
      let log_ext = log_ext kind in
      let command_string = command_string diff in
      lock_printf "Command:@\n%s@." command_string;
      if !behavior = Show
      then ignore (launch ("cat " ^ log_prefix ^ log_ext ^ ".log"))
      else
        let oracle_prefix = oracle_prefix diff in
        let diff_string =
          !do_diffs ^ " " ^
	    oracle_prefix ^ log_ext ^ ".oracle " ^
	    log_prefix ^ log_ext ^ ".log"
        in
        ignore (launch diff_string)
  | Target_error execnow ->
      lock_printf "Custom command failed: %s@\n" execnow.ex_cmd
  | Log_error(dir, file) ->
      let result_file = make_result_file dir file in
      lock_printf "Log of %s:@." result_file;
      if !behavior = Show
      then ignore (launch ("cat " ^ result_file))
      else
        let diff_string =
	  !do_diffs ^ " " ^ make_oracle_file dir file ^ " " ^ result_file
	in
        ignore (launch diff_string)


let diff_thread () =
  lock () ;
  while true do
    try
      let diff = Queue.pop shared.diffs in
      unlock ();
      do_diff diff;
      lock ()
    with Queue.Empty ->
      if shared.cmp_finished then (unlock () ; Thread.exit ());

      Condition.wait shared.diff_available shared.lock
      (* this atomically releases the lock and suspends
	 the thread on the condition cmp_available *)
  done

let test_pattern config =
  let regexp = Str.regexp config.dc_test_regexp in
  fun file ->
    Str.string_match regexp file 0

let files = Queue.create ()

(* test for a possible toplevel configuration. *)
let default_config =
  let general_config_file = Filename.concat test_path dir_config_file in
    if Sys.file_exists general_config_file
    then begin
      let scan_buffer = Scanf.Scanning.from_file general_config_file in
      scan_options Filename.current_dir_name scan_buffer default_config
    end
    else default_config

let () =
  (* enqueue the test files *)
  let suites =
    match !suites with
      [] -> default_suites
    | l -> List.rev l
  in
  List.iter
    (fun suite ->
       if !verbosity >= 2 then lock_printf "%% Now treating test %s\n%!" suite;
      (* the "suite" may be a directory in [test_path] or a single file *)
      let interpret_as_file =
	try
	  ignore (Filename.chop_extension suite);
	  true
	with Invalid_argument _ -> false
      in
      let directory =
	if interpret_as_file
	then
	  Filename.dirname suite
	else
	  Filename.concat test_path suite
      in
      let config = Filename.concat directory dir_config_file in
      let dir_config =
        if Sys.file_exists config
	then begin
	    let scan_buffer = Scanf.Scanning.from_file config in
            scan_options directory scan_buffer default_config
        end
	else default_config
      in
      if interpret_as_file
      then Queue.push (Filename.basename suite, directory, dir_config) files
      else begin
	  let dir_files = Sys.readdir directory in
	  for i = 0 to pred (Array.length dir_files) do
	    let file = dir_files.(i) in
	    assert (Filename.is_relative file);
	    if test_pattern dir_config file
	    then Queue.push (file, directory, dir_config) files;
	  done
	end)
    suites

let dispatcher () =
  try
    while true
    do
      lock ();
      while (Queue.length shared.commands) + (Queue.length shared.cmps) >= !n
      do
	Condition.wait shared.commands_empty shared.lock;
      done;
      (* we have the lock *)
      let file, directory, config = Queue.pop files in
      let config =
        scan_test_file config directory file in
      let toplevel =
	if not !use_byte
	then config.dc_toplevel
	else opt_to_byte config.dc_toplevel
      in
      let i = ref 0 in
      let make_toplevel_cmd option =
        {file=file; options = option; toplevel = toplevel;
         n = !i; directory = directory;
	 filter = config.dc_filter}
      in
      let treat_option q option =
	Queue.push
	  (Toplevel (make_toplevel_cmd option))
	  q;
	incr i
      in
      if not config.dc_dont_run
      then begin
      (match config.dc_execnow with
         | Some s ->
	     let subworkqueue = Queue.create () in
	     List.iter (treat_option subworkqueue) config.dc_options;
             Queue.push
               (Target (s, subworkqueue))
               shared.commands
         | None ->
             List.iter
	       (treat_option shared.commands)
	       config.dc_options);
      Condition.broadcast shared.work_available;
      end;
      unlock () ;
      done
  with Queue.Empty ->
    shared.commands_finished <- true;
    unlock ()

let () =
  let worker_ids = Array.init !n
    (fun _ -> Thread.create worker_thread ())
  in
  let diff_id = Thread.create diff_thread () in

  dispatcher ();
  if !behavior = Run
  then
    lock_printf "%% Dispatch finished, waiting for workers to complete@.";
  ignore (Thread.create
    (fun () ->
      while true do
	Condition.broadcast shared.work_available;
	Thread.delay 0.5;
      done)
    ());
  Array.iter Thread.join worker_ids;

  if !behavior = Run
  then
    lock_printf "%% Comparisons finished, waiting for diffs to complete@.";
  lock();
  shared.cmp_finished <- true;
  unlock();
  ignore (Thread.create
    (fun () ->
      while true do
	Condition.broadcast shared.diff_available;
	Thread.delay 0.5;
      done)
    ());
  Thread.join diff_id;
  if !behavior = Run
  then
    lock_printf "%% Diffs finished. Summary:@\nRun = %d@\nOk  = %d of %d@."
      shared.summary_run shared.summary_ok shared.summary_log;
  exit 0;


(*
Local Variables: 
compile-command: "make -j -C .. bin/regtest.byte"
End: 
*)
