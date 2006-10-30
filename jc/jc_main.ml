
open Jc_env
open Jc_ast

let test1 =
  Jc_interp.statement
    (JCSexpr (JCEconst (JCCreal "3.1415927")))

let test1 =
  Output.Def("test1",test1)
  
let main () =
  Pp.print_in_file 
    (fun fmt -> Format.fprintf fmt "%a@." Output.fprintf_why_decl test1)
    "/tmp/jessie_test1.why"


let _ = Printexc.catch main ()

  
