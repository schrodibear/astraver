
{
  open Lexing
  let string_of_option = function None -> "" | Some s -> s
}

rule split = parse
  | (['0'-'9']+ as int) '.' (['0'-'9']* as frac) 
    (['e''E'](['-''+']?['0'-'9']+ as exp))? ['f''F''d''D'] ?
      { (int, frac, string_of_option exp) }

  | '.' (['0'-'9']+ as frac) (['e''E'](['-''+']?['0'-'9']+ as exp))? 
    ['f''F''d''D'] ?
      { ("", frac, string_of_option exp) }

  | (['0'-'9']+ as int) ['e''E'] (['-''+']?['0'-'9']+ as exp) ['f''F''d''D'] ?
      { (int, "", exp) }

{
  let split s = split (from_string s)
}
