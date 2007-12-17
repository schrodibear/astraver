type 'a ref = {
  mutable contents: 'a;
}

(*let (:=) r v = r.contents <- v

let (!) r = r.contents

let ref v = { contents = v }*)

let test_int x = x.contents <- 42

let test_bool y = y.contents <- (42 >= 69)

(*
Local Variables: 
compile-command: "unset LANG; make ref"
End: 
*)
