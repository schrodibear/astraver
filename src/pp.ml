(*s Pretty-print *)

open Format

let print_option f fmt = function
  | None -> ()
  | Some x -> f fmt x

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let comma fmt () = fprintf fmt ",@ "
let semi fmt () = fprintf fmt ";@ "
let space fmt () = fprintf fmt "@ "
let alt fmt () = fprintf fmt "|@ "
let newline fmt () = fprintf fmt "@\n"
let arrow fmt () = fprintf fmt "@ -> "
let nothing fmt () = ()
let string fmt s = fprintf fmt "%s" s

let hov n fmt f x = pp_open_hovbox fmt n; f x; pp_close_box fmt ()

let print_in_file ?(margin=78) p f =
  let cout = open_out f in
  let fmt = formatter_of_out_channel cout in
  pp_set_margin fmt margin;
  pp_open_box fmt 0; p fmt; pp_close_box fmt ();
  pp_print_flush fmt ();
  close_out cout
