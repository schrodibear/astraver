type input_kind = Ml | Mli

let input_files = ref []

(******************************************************************************)

let input_file t n = input_files := (t, n) :: !input_files

let spec = Arg.align [
  "-ml", Arg.String(input_file Ml),
  "<file> Input file assuming it is a structure";
  "-mli", Arg.String(input_file Mli),
  "<file> Input file assuming it is a signature";
]

let file_ext f =
  let i = ref (String.length f - 1) in
  while !i >= 0 && f.[!i] <> '.' do i := !i - 1 done;
  match if !i < 0 then "" else String.sub f !i (String.length f - !i) with
    | ".mli" -> Mli
    | _ -> Ml

let anon_fun s = input_file (file_ext s) s

let usage_msg = "jessica [options] files"

let _ =
  Arg.parse spec anon_fun usage_msg

(******************************************************************************)

let input_files = !input_files

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
