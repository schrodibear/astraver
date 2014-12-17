
open Format

let nvalid = ref 0
let ninvalid = ref 0
let nunknown = ref 0
let ntimeout = ref 0
let nfailure = ref 0

let wallclock = ref 0.0
let cpu = ref 0.0

let one_line s = 
  try 
    Scanf.sscanf s "valid   : %3d" (fun x -> nvalid := x + !nvalid)
  with _ -> try
    Scanf.sscanf s "invalid : %3d" (fun x -> ninvalid := x + !ninvalid)
  with _ -> try
    Scanf.sscanf s "unknown : %3d" (fun x -> nunknown := x + !nunknown)
  with _ -> try
    Scanf.sscanf s "timeout : %3d" (fun x -> ntimeout := x + !ntimeout)
  with _ -> try
    Scanf.sscanf s "failure : %3d" (fun x -> nfailure := x + !nfailure)
  with _ -> try
    Scanf.sscanf s "total wallclock time : %f sec" 
      (fun s -> wallclock := !wallclock +. s)
  with _ -> try
    Scanf.sscanf s "total wallclock time : %d m %d sec" 
      (fun m s -> wallclock := !wallclock +. 60. *. float m +. float s)
  with _ -> try
    Scanf.sscanf s "total wallclock time : %d h %d m %d sec" 
      (fun h m s -> wallclock := !wallclock +. 
	 3600. *. float h +. 60. *. float m +. float s)
  with _ -> try
    Scanf.sscanf s "total CPU time       : %f sec" 
      (fun s -> cpu := !cpu +. s)
  with _ -> try
    Scanf.sscanf s "total CPU time       : %d m %d sec" 
      (fun m s -> cpu := !cpu +. 60. *. float m +. float s)
  with _ -> try
    Scanf.sscanf s "total CPU time       : %d h %d m %d sec" 
      (fun h m s -> cpu := !cpu +. 
	 3600. *. float h +. 60. *. float m +. float s)
  with _ ->
    ()

let one_file f =
  let c = open_in f  in
  try
    while true do one_line (input_line c) done
  with End_of_file ->
    close_in c

let print_time fmt f =
  if f < 60.0 then fprintf fmt "%.2f sec" f else 
    let t = int_of_float f in
    let m = t / 60 in
    let s = t mod 60 in
    if f < 3600.0 then fprintf fmt "%d m %02d sec" m s else 
      let h = m / 60 in
      let m = m mod 60 in
      fprintf fmt "%d h %02d m %02d sec" h m s  

let () =
  for i = 1 to Array.length Sys.argv - 1 do one_file Sys.argv.(i) done;
  let n = !nvalid + !ninvalid + !ntimeout + !nunknown + !nfailure in
  if n = 0 then exit 0;
  let pvalid = 100. *. float !nvalid /. float n in
  let pinvalid = 100. *. float !ninvalid /. float n in
  let ptimeout = 100. *. float !ntimeout /. float n in
  let punknown = 100. *. float !nunknown /. float n in
  let pfailure = 100. *. float !nfailure /. float n in
  Format.printf 
"total   : %3d
valid   : %3d (%3.0f%%)
invalid : %3d (%3.0f%%)
unknown : %3d (%3.0f%%)
timeout : %3d (%3.0f%%)
failure : %3d (%3.0f%%)@." n
    !nvalid pvalid !ninvalid pinvalid !nunknown punknown 
    !ntimeout ptimeout !nfailure pfailure;
  Format.printf
"total wallclock time : %a
total CPU time       : %a@."
    print_time !wallclock print_time !cpu


