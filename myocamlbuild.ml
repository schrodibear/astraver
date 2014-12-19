open Ocamlbuild_plugin;;
open Ocamlbuild_pack;;

dispatch @@
function
| Before_options ->
  Options.ocamldep := A"../ocamldep"
| After_rules ->
  Slurp.slurp "src/jc" |>
  begin function
  | Slurp.Dir (_, _ ,_ ,_, l) ->
    ListLabels.iter
      (Lazy.force l)
      ~f:(function
        | Slurp.File (path, name, _, _) ->
          non_dependency "src/jc/jc.ml" @@ module_name_of_pathname (path / name)
        | _ -> ())
  | _ -> ()
  end
| _ -> ()
