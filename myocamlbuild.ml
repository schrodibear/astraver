(* List of projects in the Why platform, with their main target *)
let targets = [
  "why", "src/main";
  "caduceus", "c/cmain";
  "jessie", "jc/jc_main";
  "krakatoa", "java/java_main";
  "jessica", "ml/ml_main";
  "demixify", "mix/mix_main";
  "gwhy", "intf/stat";
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
  "src", ["tools"; "jc"];
  "tools", ["src"];
  "jc", ["src"];
  "java", ["src"; "jc"];
  "c", ["jc"; "src"];
  "ml", ["jc"; "src"];
  "ml/parsing", ["ml/utils"];
  "ml/typing", ["ml/parsing"; "ml/utils"];
  "mix", ["src"];
  "intf", ["src"; "tools"];
]

(* List of findlib packages that are automatically used *)
let default_packages = [
  "unix";
  "num";
  "str";
  "ocamlgraph";
]

(* List of packages that are not automatically used (use the pkg_* tag) *)
let other_packages = [
  "threads";
  "lablgtk2";
]

(******************************************************************************)

open Ocamlbuild_plugin

let ocamlfind x = S [
  A "ocamlfind";
  x;
  A "-package";
  A (String.concat "," default_packages);
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

      (* Declare pkg_* tags *)
      List.iter
	(fun pkg ->
	   flag ["ocaml"; "pkg_"^pkg; "compile"] & S[A "-package"; A pkg];
	   flag ["ocaml"; "pkg_"^pkg; "link"] & S[A "-package"; A pkg])
	other_packages;

      (* Special flag for threads *)
      (* (don't use the "thread" tag which doesn't work well with findlib) *)
      flag ["ocaml"; "pkg_threads"; "compile"] (S[A "-thread"]);
      flag ["ocaml"; "pkg_threads"; "link"] (S[A "-thread"]);

      (* Use the -linkpkg option when linking *)
      flag ["ocaml"; "link"] (A "-linkpkg")
  | _ -> ()
end

(*
  Local Variables:
  compile-command: "unset LANG; EMACS=yes make -f build.makefile"
  End:
*)
