(* List of projects in the Why platform, with their main target *)
let targets = [
  "why", "src/main";
  "caduceus", "c/cmain";
  "jessie", "jc/jc_main";
  "krakatoa", "java/java_main";
  "jessica", "ml/ml_main";
  "demixify", "mix/mix_main";
  (* tools *)
  "why2html", "tools/why2html";
  "dp", "tools/dp";
  "rv_merge", "tools/rv_merge";
  "why-obfuscator", "tools/obfuscator";
  "simplify2why", "tools/simplify_towhy";
  "why-stat", "tools/whystat";
]

(* List of scripts that generate files, their dependencies,
and the files they generate. *)
let generating_scripts = [
  "version.sh",
  [ "Version" ],
  [ "src/version.ml";
    "jc/jc_version.ml";
    "java/java_version.ml";
    "c/cversion.ml" ];
  "jc_ai.sh",
  [ "jc/jc_annot_inference.ml";
    "jc/jc_annot_fail.ml" ],
  [ "jc/jc_ai.ml" ];
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
  "mix", ["src"];
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

let execute_script x =
  Seq[
    Cmd(Sh("chmod u+x "^x));
    Cmd(Sh("./"^x));
  ]

let _ = dispatch begin function
  | Before_hygiene ->
      (* Declare contexts *)
      List.iter (fun (a, b) -> Pathname.define_context a b) contexts

  | After_options ->
      (* Use findlib *)
      Options.ocamlc := ocamlfind & A "ocamlc";
      Options.ocamlopt := ocamlfind & A "ocamlopt";
      Options.ocamldep := ocamlfind & A "ocamldep";
      Options.ocamldoc := ocamlfind & A "ocamldoc";

  | After_rules ->
      (* Rules for our targets *)
      List.iter
	(fun (target, dep) ->
	   rule (dep^" -> "^target)
	     ~insert:`top
	     ~dep:dep
	     ~prod:target
	     (fun _ _ -> Seq [
		cp dep target;
		cp target ("../bin/"^target);
	      ]))
	targets;

      (* Rules for scripts that generate files *)
      List.iter
	(fun (script, deps, files) ->
	   rule (script^" -> "^String.concat ", " files)
	     ~insert:`top
	     ~deps:(script::deps)
	     ~prods:files
	     (fun _ _ -> execute_script script))
	generating_scripts;

      (* Use the -linkpkg option when linking *)
      flag ["ocaml"; "link"] (A "-linkpkg")
  | _ -> ()
end

(*
  Local Variables:
  compile-command: "unset LANG; EMACS=yes make -f build.makefile"
  End:
*)
