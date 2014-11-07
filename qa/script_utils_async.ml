
open Core.Std
open Async.Std

let re = Str.regexp
let matches r s = Str.string_match r s 0

let input_lines ?(rev=false) =
  Fn.compose
    (Deferred.map
       ~f:(if rev then List.rev
                  else Fn.id))
    @@
    function
    | `filename s -> Reader.file_lines s
    | `out p | `err p as reader ->
      Pipe.to_list @@ Reader.lines @@ Process.(match reader with `out _ -> stdout | `err _ -> stderr) p

let write_file filename ?append str =
  Writer.with_file ?append ~exclusive:true filename
    ~f:(fun t -> Deferred.return @@ Writer.write_line t str)

let pr format = Writer.(writef (Lazy.force stdout) format)
let spr = Printf.sprintf
