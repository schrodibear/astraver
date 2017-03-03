#!/usr/bin/env ocamlscript
Ocaml.packs := ["jingoo"]
--

let () =
  if Array.length Sys.argv < 2 then
    Printf.eprintf "Usage:%s <file.tmpl>" Sys.argv.(0)
  else
    let template = Sys.argv.(1) in
    let out = open_out @@ Filename.(remove_extension template) ^ ".gen" in
    output_string out @@ Jg_template.from_file template;
    close_out out
