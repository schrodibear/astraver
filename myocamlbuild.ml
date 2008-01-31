open Ocamlbuild_plugin;;

dispatch begin function
  | After_rules ->
      Pathname.define_context "ml/parsing"
	["ml/parsing"; "ml/utils"];
      Pathname.define_context "ml/typing"
	["ml/parsing"; "ml/utils"]
  | _ -> ()
end
