(* List of projects in the Why platform, with their main target *)
let targets = [
  "why", "src/main";
  "jessie", "jc/jc_main";
  "krakatoa", "java/java_main";
  "jessica", "ml/ml_main";
  "caduceus", "c/cmain";
]

(* List of external libraries *)
(* Don't forget to update the _tags file(s) too *)
let libraries = [
  "graph";
]

(******************************************************************************)

open Ocamlbuild_plugin

let targets =
  let targets_byte = List.map
    (fun (a, b) -> a^".byte", b^".byte")
    targets
  in
  let targets_native = List.map
    (fun (a, b) -> a^".opt", b^".native")
    targets
  in
  targets_byte @ targets_native

let find_dep target targets =
  try
    List.assoc target targets
  with Not_found ->
    Printf.printf "No rule for Why binary: %s\n%!" target;
    exit 1

let build_dep _build dep =
  match _build [[dep]] with
    | [Outcome.Good path] -> ()
    | [Outcome.Bad e] -> raise e
    | _ -> failwith "myocamlbuild.ml: build_dep"

let _ = dispatch begin function
  | After_rules ->
      (* Special rules for Jessica because of potential name clashes *)
      Pathname.define_context "ml/parsing"
	["ml/parsing"; "ml/utils"];
      Pathname.define_context "ml/typing"
	["ml/typing"; "ml/parsing"; "ml/utils"];

      (* External libraries *)
      List.iter (ocaml_lib ~extern:true) libraries;

      (* Remove the "ocaml" tag from our targets *)
      List.iter	(fun (f, _) -> tag_file f ["-ocaml"]) targets;

      (* Rules for our targets *)
      List.iter
	(fun (target, dep) ->
	   rule (dep^" -> "^target)
	     ~insert:`top (* doesn't seem to be needed *)
	     ~prod:target
	     begin fun env _build ->
	       build_dep _build dep;
	       cp dep target
	     end)
	targets
  | _ -> ()
end
