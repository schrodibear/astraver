(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.ml,v 1.5 2002-03-12 16:05:25 filliatr Exp $ i*)

open Format

let verbose = ref false

let if_verbose f x = if !verbose then f x
let if_verbose_2 f x y = if !verbose then f x y
let if_verbose_3 f x y z = if !verbose then f x y z

let debug = ref false

let if_debug f x = if !debug then f x
let if_debug_2 f x y = if !debug then f x y
let if_debug_3 f x y z = if !debug then f x y z

(*i
let null_formatter = make_formatter (fun _ _ _ -> ()) (fun _ -> ())
let dprintf f = if !debug then eprintf f else fprintf null_formatter f
i*)

let parse_only = ref false

let type_only = ref false

let wp_only = ref false

type prover = Coq | Pvs

let prover = ref Coq

