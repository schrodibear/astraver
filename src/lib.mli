
val mkdir_p : string -> unit

(* [file subdir file]: if file is "dirname/basename", inserts subdir dirname
   and basename, resulting in filename "dirname/subdir/basename";
   creates directory "dirname/subdir" if it does not exist *)
val file : subdir:string -> file:string -> string

