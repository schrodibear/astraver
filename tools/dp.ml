
(* script to call Simplify and CVC Lite *)

open Printf

let timeout = ref 10
let debug = ref false
let files = Queue.create ()

let spec = 
  [ "-timeout", Arg.Int ((:=) timeout), "<int>  set the timeout (in seconds)";
    "-debug", Arg.Set debug, "set the debug flag" ]
let usage = "usage: dp [options] files.{cvc,cvc.all,sx,sx.all}"
let () = Arg.parse spec (fun s -> Queue.push s files) usage 

(* stats *)
let nvalid = ref 0
let ninvalid = ref 0
let ntimeout = ref 0

let call_cvcl f =
  assert false

let call_simplify f =
  let cmd = sprintf "ulimit -t %d; Simplify %s > out && grep -q Valid out" !timeout f in
  if !debug then begin eprintf "calling: %s\n" cmd; flush stderr end;
  let out = Sys.command cmd in
  if out = 0 then begin printf "valid\n"; incr nvalid end
  else if out = 1 then begin printf "invalid\n"; incr ninvalid end
  else begin printf "timeout\n"; incr ntimeout end;
  flush stdout

let split f =
  if Filename.check_suffix f ".cvc"  || Filename.check_suffix f ".cvc.all" then
    Cvcl_split.iter call_cvcl f 
  else 
  if Filename.check_suffix f ".sx" || Filename.check_suffix f ".sx.all" then
    Simplify_split.iter call_simplify f 
  else 
    begin Arg.usage spec usage; exit 1 end

let main () = 
  Queue.iter split files;
  printf "valid = %d \t invalid = %d \t timeout = %d\n" 
    !nvalid !ninvalid !ntimeout

let () = Printexc.catch main ()
