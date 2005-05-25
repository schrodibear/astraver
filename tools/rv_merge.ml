
(* merge several haRVey files into a single one *)

open Printf

let usage () =
  eprintf "usage: rv_merge file1.rv ... filen.rv\n";
  exit 1

let queue = Queue.create ()

let () =
  for i = 1 to Array.length Sys.argv - 1 do
    let f = Sys.argv.(i) in
    if not (Filename.check_suffix f ".rv") then usage ();
    Queue.add (open_in f) queue
  done

let copy_theory c =
  ignore (input_line c); (* skip first line : ( ;; BEGIN THEORY ) *)
  try
    while true do
      let s = input_line c in
      if s = ") ;; END THEORY" then raise Exit;
      printf "%s\n" s
    done
  with Exit -> 
    ()

let copy_goals c =
  try
    while true do let s = input_line c in printf "%s\n" s done
  with End_of_file -> 
    close_in c;
    printf "\n\n"

let () =
  printf "(\n";
  Queue.iter copy_theory queue;
  printf ") ;; END THEORY\n\n";
  Queue.iter copy_goals queue

