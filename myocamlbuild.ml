open Ocamlbuild_plugin;;
open Ocamlbuild_pack;;

let get_pathnames path =
  let open Slurp in
  let get_pathnames l =
    ListLabels.map
      (!* l)
      ~f:(function
        | File (path, name, _, _) -> [path / name]
          | _ -> [])
    |>
    List.concat
  in
  slurp path |>
  function
  | Dir (_, _, _, _, l) ->
    begin match List.hd @@ !* l with
    | Dir (_, _, _, _, l) -> get_pathnames l
    | File _ -> get_pathnames l
    | _ -> []
    end
  | _ -> [];;

let jc_pathnames = get_pathnames "src/jc";;

let why_pathnames = get_pathnames "src/why";;

let rec slow_uniq =
  function
  | [] -> []
  | x :: xs -> x :: (slow_uniq @@ List.filter ((<>) x) xs);;

let (%) f g x = f (g x);;

dispatch @@
function
| Before_options ->
  Options.ocamldep := A"../ocamldep";
  Options.ocaml_pkgs := ["num"; "ocamlgraph"; "str"; "unix"]
| Before_rules ->
  let includes = [A "-a"; A "-I"; A "src/jc"; A "-I"; A "src/why"] in
  let cmxs =
    let open List in
    let open Pathname in
    why_pathnames @ jc_pathnames |>
    map basename |>
    filter ((<>) "mli" % get_extension) |>
    map remove_extension |>
    slow_uniq |>
    map (add_extension "cmx") |>
    filter (fun file -> exists @@ "_build/src/jc/" / file || exists @@ "_build/src/why" / file)
  in
  let to_params = List.map (fun file -> P file) in
  rule "build cmxa"
    ~prod:"%.cmxa"
    ~deps:["%.cmx"]
    (fun env build ->
      Cmd (S (!Options.ocamlopt :: A "-linkall" :: includes @ to_params cmxs @ [A "-o"; P (env "%.cmxa")])));
  let cmos =
    List.map Pathname.(add_extension "cmo" % remove_extension) cmxs
  in
  rule "build cma"
    ~prod:"%.cma"
    ~deps:["%.cmo"]
    (fun env build ->
      Cmd (S (!Options.ocamlc :: A "-linkall" :: includes @ to_params cmos @ [A "-o"; P (env "%.cma")])));
| After_rules ->
  List.iter (fun pathname -> non_dependency "src/jc/jc.ml" @@ module_name_of_pathname pathname) jc_pathnames
| _ -> ()
