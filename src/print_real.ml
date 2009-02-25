
open Format
open Big_int
open Logic

let print_decimal_no_exponent fmt = function
  | "","0",_ | "0","",_ | "0","0",_ -> 
      fprintf fmt "0.0"
  | "",f, None -> 
      fprintf fmt "0.%s" f
  | i,"", None -> 
      fprintf fmt "%s.0" i
  | i,f, None ->
      fprintf fmt "%s.%s" i f      
  | i,f, Some e ->
      let e = (int_of_string e) - String.length f in
      if e = 0 then
	fprintf fmt "%s%s" i f
      else if e > 0 then
	fprintf fmt "(%s%s * 1%s)" i f (String.make e '0')
      else
	fprintf fmt "(%s%s / 1%s)" i f (String.make (-e) '0')

let print_no_exponent fmt = function
  | RConstDecimal (i, f, e) -> print_decimal_no_exponent fmt (i,f,e)
  | RConstHexa (i, f, e) -> (* print_hexa fmt i f e *) assert false (*TODO*)

let hexa_to_decimal s =
  let n = String.length s in
  let rec compute acc i =
    if i = n then 
      acc 
    else 
      compute (add_int_big_int 
		  (match s.[i] with 
		    | '0'..'9' as c -> Char.code c - Char.code '0'
		    | 'A'..'F' as c -> 10 + Char.code c - Char.code 'A'
		    | 'a'..'f' as c -> 10 + Char.code c - Char.code 'a'
		    | _ -> assert false)
		  (mult_int_big_int 16 acc)) (i+1)
  in
  string_of_big_int (compute zero_big_int 0)

let power2 n =
  string_of_big_int (power_int_positive_int 2 n)

let print_with_integers exp0_fmt exp_pos_fmt exp_neg_fmt fmt = function
  | RConstDecimal (i, f, e) -> 
      let f = if f = "0" then "" else f in
      let e = 
	(match e with None -> 0 | Some e -> int_of_string e) - 
	String.length f 
      in
      if e = 0 then
	fprintf fmt exp0_fmt (i ^ f)
      else if e > 0 then
	fprintf fmt exp_pos_fmt (i ^ f) ("1" ^ String.make e '0')
      else
	fprintf fmt exp_neg_fmt (i ^ f) ("1" ^ String.make (-e) '0')
  | RConstHexa (i, f, e) -> 
      let f = if f = "0" then "" else f in
      let dec = hexa_to_decimal (i ^ f) in
      let e = int_of_string e - 4 * String.length f in
      if e = 0 then
	fprintf fmt exp0_fmt dec
      else if e > 0 then
	fprintf fmt exp_pos_fmt dec (power2 e)
      else
	fprintf fmt exp_neg_fmt dec (power2 (-e))
      

let print fmt = function
  | RConstDecimal (i, f,None) -> 
      fprintf fmt "%s.%s" i f 
  | RConstDecimal (i, f, Some e) -> 
      fprintf fmt "%s.%se%s" i f e
  | RConstHexa (i, f, e) -> 
      fprintf fmt "0x%s.%sp%s" i f e

