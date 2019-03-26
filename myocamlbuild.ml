open Ocamlbuild_plugin;;
open Ocamlbuild_pack;;

open StdLabels;;

let (%) f g x = f (g x);;

let (%>) g f x = f (g x);;

let get_files =
  let open Slurp in
  let rec traverse l =
    l |>
    List.map
      ~f:(function
        | Dir (_, _, _, _, l) -> traverse (!* l)
        | File (path, name, _, _) -> [path / name]
        | Error _ | Nothing -> [])
    |>
    List.concat
  in
  slurp %>
  (fun a -> [a]) %>
  traverse;;

dispatch @@
function
| After_options ->
  Options.ocamldep := A "../ocamldep"
| After_rules ->
  get_files "src/av" |>
  List.iter ~f:(non_dependency "src/av/aliases.mli" % module_name_of_pathname)
| _ -> ()
