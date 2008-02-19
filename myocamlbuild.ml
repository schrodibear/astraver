(* List of projects in the Why platform, with their main target *)
let targets = [
  "why", "src/main";
  "jessie", "jc/jc_main";
  "krakatoa", "java/java_main";
  "jessica", "ml/ml_main";
  "caduceus", "c/cmain";
]

(* Some directories "see" some other directories *)
let contexts = [
  "src", ["tools"];
  "tools", ["src"];
  "jc", ["src"];
  "java", ["src"; "jc"];
  "c", ["jc"; "src"];
  "ml", ["jc"; "src"];
  "ml/parsing", ["ml/utils"];
  "ml/typing", ["ml/parsing"; "ml/utils"];
]

(* List of libraries (for findlib) *)
let libraries = [
  "unix";
  "num";
  "str";
  "ocamlgraph";
]

(******************************************************************************)

open Ocamlbuild_plugin

let ocamlfind x = S [
  A "ocamlfind";
  x;
  A "-package";
  A (String.concat "," libraries);
]

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

let _ = dispatch begin function
  | Before_hygiene ->
      (* Declare contexts *)
      List.iter (fun (a, b) -> Pathname.define_context a b) contexts

  | After_options ->
      (* Use findlib *)
      Options.ocamlc := ocamlfind & A "ocamlc";
      Options.ocamlopt := ocamlfind & A "ocamlopt";

  | After_rules ->
      (* Rules for our targets *)
      List.iter
	(fun (target, dep) ->
	   rule (dep^" -> "^target)
	     ~insert:`top
	     ~dep:dep
	     ~prod:target
	     (fun env _build -> cp dep target))
	targets;

      (* Use the -linkpkg option when linking *)
      flag ["ocaml"; "link"] (A "-linkpkg")
  | _ -> ()
end

(*
  Local Variables:
  compile-command: "unset LANG; EMACS=yes make -f build.makefile"
  End:
*)
