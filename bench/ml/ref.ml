type 'a ref = {
  mutable contents: 'a;
}

let (:=) r v = r.contents <- v

let (!) r = r.contents

let ref v = { contents = v }

let test x = x := 42

(*
Local Variables: 
compile-command: "unset LANG; make ref"
End: 
*)
