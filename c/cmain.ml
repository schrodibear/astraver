
open Format
open Cerror
open Creport

let parse_only = ref false
let cpp_command = ref "gcc -E"

(* C pre-processor *)
let cpp inf outf = 
  ignore (Sys.command (sprintf "%s %s > %s" !cpp_command inf outf))

let files = Queue.create ()
let add_file f = Queue.add f files

let interp_file f =
  Loc.set_file f;
  let ppf = Filename.temp_file (Filename.basename f) ".i" in
  try
    cpp f ppf;
    let c = open_in ppf in
    let d = Clexer.parse c in
    if !parse_only then raise Exit;
    let p = Cinterp.interp d in
    ()
  with e ->
    Sys.remove ppf;
    raise e

let _ = 
  Arg.parse 
      [ "-parse-only", Arg.Set parse_only, "  stops after parsing" ]
      add_file "caduceus [options] file..."

let main () = Queue.iter (fun f -> try interp_file f with Exit -> ()) files

let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Error (Some loc, e) | Stdpp.Exc_located (_, Error (Some loc, e)) ->
      fprintf fmt "%a%a" Loc.report loc report e
  | Stdpp.Exc_located (loc, e) ->
      fprintf fmt "%a%a" Loc.report loc explain_exception e
  | Error (_, e) ->
      report fmt e
  | e ->
      fprintf fmt "Anomaly: %s" (Printexc.to_string e); raise e

let () =
  try
    main ()
  with e ->
    eprintf "%a@." explain_exception e;
    exit 1
