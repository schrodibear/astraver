
(* small library common to Why and Caduceus *)

let mkdir_p dir =
  if Sys.file_exists dir then begin
    if (Unix.stat dir).Unix.st_kind <> Unix.S_DIR then
      failwith ("failed to create directory " ^ dir)
  end else
    Unix.mkdir dir 0o777

let file ~subdir ~file = 
  let dir = Filename.concat (Filename.dirname file) subdir in
  mkdir_p dir;
  Filename.concat dir (Filename.basename file)

