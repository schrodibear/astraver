
let parse_only = ref false
let type_only = ref false
let cpp_command = ref "gcc -E"
let with_cpp = ref true
let debug = ref false
let verbose = ref false

let files = Queue.create ()
let add_file f = Queue.add f files

let _ = 
  Arg.parse 
      [ "-parse-only", Arg.Set parse_only, 
	  "  stops after parsing";
        "-type-only", Arg.Set type_only, 
	  "  stops after typing";
        "-no-cpp", Arg.Clear with_cpp, 
	  "  no C preprocessor";
        "-ccp", Arg.String ((:=) cpp_command), 
	  " <cmd>  sets the C preprocessor";
	"-d", Arg.Set debug,
          "  debugging mode" ]
      add_file "caduceus [options] file..."

let parse_only = !parse_only
let type_only = !type_only
let debug = !debug
let verbose = !verbose
let with_cpp = !with_cpp
let cpp_command = !cpp_command
