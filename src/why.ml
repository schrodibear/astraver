
open Format
open Main

let _ =
  try
    main ()
  with e ->
    Report.explain_exception err_formatter e;
    pp_print_newline err_formatter ();
    exit 1
