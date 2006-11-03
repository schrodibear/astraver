
(* $Id: jc_envset.ml,v 1.1 2006-11-03 16:27:06 marche Exp $ *)

open Jc_env

module FieldSet = 
  Set.Make(struct type t = field_info
		  let compare f1 f2 = 
		    Pervasives.compare 
		      f1.jc_field_info_tag f2.jc_field_info_tag
	   end)

