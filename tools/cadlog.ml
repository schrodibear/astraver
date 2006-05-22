
open Format
open Cversion
open Unix

let c = match Sys.argv with
  | [| _; f |] -> open_out f
  | _ -> eprintf "usage: cadlog file@."; exit 1

let fmt = formatter_of_out_channel c

let d,m,y =
  let tm = localtime (time ()) in
    tm.tm_mday, 1+tm.tm_mon, tm.tm_year

let () =
  fprintf fmt "Caduceus version: %s@." version;
  fprintf fmt "Caduceus compilation date: %s@." date;
  fprintf fmt "Caduceus compilation date: %d/%d/%d@." d m y;
  try
    while true do
      let s = read_line () in
	print_endline s;
	fprintf fmt "%s@." s
    done
  with End_of_file ->
    close_out c
