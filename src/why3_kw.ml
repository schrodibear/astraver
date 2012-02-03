
let is_why3_keyword =
  let ht = Hashtbl.create 43 in
  List.iter (fun kw -> Hashtbl.add ht kw ())
    [
        "as";
        "axiom";
        "clone";
        "else";
        "end";
        "epsilon";
        "exists";
        "export";
        "false";
        "forall";
        "function";
        "goal";
        "if";
        "import";
        "in";
        "inductive";
        "lemma";
        "let";
        "match";
        "meta";
        "namespace";
        "not";
        "predicate";
        "prop";
        "then";
        "theory";
        "true";
        "type";
        "use";
        "with";
        "abstract";
        "absurd";
        "any";
        "assert";
        "assume";
        "begin";
        "check";
        "do";
        "done";
        "downto";
        "exception";
        "for";
        "fun";
        "invariant";
        "label";
        "loop";
        "model";
        "module";
        "mutable";
        "raise";
        "raises";
        "reads";
        "rec";
        "to";
        "try";
        "val";
        "variant";
        "while";
        "writes";
    ];
  Hashtbl.mem ht

