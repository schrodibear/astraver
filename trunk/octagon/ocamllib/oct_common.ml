(* oct_common.ml
   Abstract semantics functions and OCaml pretty-printing.

   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/
   
   Copyright (C) Antoine Mine' 2000-2002  
*)

(******************************)
(* This is from oct_common.ml *)
(******************************)

(* initialization *)
external init: unit -> bool = "ocaml_oct_init"


(* numerical domain *)
type num
type vnum

external num_of_int: int -> num = "ocaml_num_int"
external num_of_frac: int*int -> num = "ocaml_num_frac"
external num_of_float: float -> num = "ocaml_num_float"
external num_infty: unit -> num = "ocaml_num_infty"

external vnum_of_int: int array -> vnum = "ocaml_vnum_int"
external vnum_of_frac: int*int array -> vnum = "ocaml_vnum_frac"
external vnum_of_float: float array -> vnum = "ocaml_vnum_float"

external vnum_of_int_opt: int option array -> vnum = "ocaml_vnum_int_opt"
external vnum_of_frac_opt: int*int option array -> vnum = "ocaml_vnum_frac_opt"

external string_of_num: num -> string = "ocaml_num_string"
external string_of_vnum: vnum -> int -> string = "ocaml_vnum_string"
external vnum_length: vnum -> int = "ocaml_vnum_length"

external int_of_num: num -> int option = "ocaml_int_num"
external frac_of_num: num -> int*int option = "ocaml_frac_num"
external float_of_num: num -> float = "ocaml_float_num"

external int_of_vnum: vnum -> int option array = "ocaml_int_vnum"
external frac_of_vnum: vnum -> int*int option array = "ocaml_frac_vnum"
external float_of_vnum: vnum -> float array = "ocaml_float_vnum"

let fnumprinter f o =
  Format.fprintf f "@[%s@]" (string_of_num o)

let fvnumprinter f o =
  let n = vnum_length o in
  Format.fprintf f "@[[ @[";
  for i=0 to n-1 do
    if i=0 then Format.fprintf f "@[%s@]" (string_of_vnum o i)
    else Format.fprintf f ", @[%s@]" (string_of_vnum o i)
  done;
  Format.fprintf f "@] ]@]"

let numprinter = fnumprinter Format.std_formatter
let vnumprinter = fvnumprinter Format.std_formatter


(* boolean lattice *)
type tbool = Bottom | True | False | Top

(* abstract types of regular & minimized octagons *)
type oct
type moct

(* octagon creation *)
external empty:    int -> oct = "ocaml_oct_empty"
external universe: int -> oct = "ocaml_oct_universe"

(* query functions *)
external dim:           oct -> int = "ocaml_oct_dim"
external nbconstraints: oct -> int = "ocaml_oct_nbconstraints"
external get_elem:      oct -> int -> int -> num = "ocaml_oct_get_elem"
(* ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)
external get_tag:       oct -> int -> int -> bool = "ocaml_oct_get_tag"
external get_tag2:      oct -> int -> int -> bool = "ocaml_oct_get_tag2"
external nbtags:        oct -> int = "ocaml_oct_nbtags"
external hastags:       oct -> bool = "ocaml_oct_hastags"
external hastags2:       oct -> bool = "ocaml_oct_hastags2"
external remove_tags:   oct -> oct = "ocaml_oct_remove_tags"
external makeall_tags:   oct -> oct = "ocaml_oct_makeall_tags"
external remove_tagged_constraints:   oct -> oct = "ocaml_oct_remove_tagged_constraints"
external remove_untagged_constraints:   oct -> oct = "ocaml_oct_remove_untagged_constraints"
external print_tags:    oct -> unit = "ocaml_oct_print_tags"
external get_restrained_vars: oct -> vnum = "ocaml_oct_get_restrained_vars"
external get_tagged_vars: oct -> vnum = "ocaml_oct_get_tagged_vars"
external get_untagged_vars: oct -> vnum = "ocaml_oct_get_untagged_vars"
(* END ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)

(* tests *)
external is_empty: oct -> bool = "ocaml_oct_is_empty"
external is_empty_lazy: oct -> tbool= "ocaml_oct_is_empty_lazy"
external is_universe: oct -> bool= "ocaml_oct_is_universe"
external is_included_in: oct -> oct -> bool= "ocaml_oct_is_included_in"
(* ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)
external is_contextually_included_in: oct -> oct -> bool= "ocaml_oct_is_contextually_included_in"
(* END ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)
external is_included_in_lazy: 
  oct -> oct -> tbool= "ocaml_oct_is_included_in_lazy"
external is_equal: oct -> oct -> bool= "ocaml_oct_is_equal"
external is_equal_lazy: oct -> oct -> tbool= "ocaml_oct_is_equal_lazy"
external is_in: oct -> vnum -> bool= "ocaml_oct_is_in"

(* operators *)
type wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum
external inter: oct -> oct -> oct = "ocaml_oct_inter"
external union: oct -> oct -> oct = "ocaml_oct_union"
external widening: oct -> oct -> wident -> oct = "ocaml_oct_widening"
external narrowing: oct -> oct -> oct = "ocaml_oct_narrowing"
(* ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)
external subtract: oct -> oct -> oct = "ocaml_oct_subtract"
external complete: oct -> oct -> oct = "ocaml_oct_complete"
(* END ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)

(* transfer function *)
type constr = 
    PX of int*num         (*   x  <= c *)
  | MX of int*num         (*  -x  <= c *)
  | PXPY of int*int*num   (*  x+y <= c *)
  | PXMY of int*int*num   (*  x-y <= c *)
  | MXPY of int*int*num   (* -x+y <= c *)
  | MXMY of int*int*num   (* -x-y <= c *)
external forget: oct -> int -> oct = "ocaml_oct_forget"
external add_bin_constraints: 
  oct -> constr array -> oct = "ocaml_oct_add_bin_constraints"
external assign_var: oct -> int -> vnum -> oct = "ocaml_oct_assign_variable"
external substitute_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_substitute_variable"
external add_constraint: 
  oct -> vnum -> oct = "ocaml_oct_add_constraint"
external interv_assign_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_interv_assign_variable"
external interv_add_constraint: 
  oct -> vnum -> oct = "ocaml_oct_interv_add_constraint"
external interv_substitute_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_interv_substitute_variable"
(* ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)
external add_tagged_constraint: oct -> vnum -> oct = "ocaml_oct_add_tagged_constraint"
external fourier_motzkin: oct -> int -> oct = "ocaml_oct_fourier_motzkin"
(* END ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)

(* change of dimensions *)
external add_dims_and_embed: 
  oct -> int -> oct = "ocaml_oct_add_dimensions_and_embed"
external add_dims_and_project: 
  oct -> int -> oct = "ocaml_oct_add_dimensions_and_project"
external del_dims: 
  oct -> int -> oct = "ocaml_oct_remove_dimensions"

(* change of dimensions at arbitrary positions *)
type dimsup = { pos:int; nbdims:int; }
external add_dims_and_embed_multi: 
  oct -> dimsup array -> oct = "ocaml_oct_add_dimensions_and_embed_multi"
external add_dims_and_project_multi: 
  oct -> dimsup array -> oct = "ocaml_oct_add_dimensions_and_project_multi"
external del_dims_multi: 
  oct -> dimsup array -> oct = "ocaml_oct_remove_dimensions_multi"

(* normal form *)
external close: oct -> oct = "ocaml_oct_close"
(* ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)
external close_sub: oct -> vnum -> oct = "ocaml_oct_close_sub"
external close_full: oct -> oct = "ocaml_oct_close_full"
external is_closed: oct -> bool = "ocaml_oct_is_closed"
(* END ADDED WHEN OCT_USE_TAG IS DEFINED IN C *)

(* interval functions *)
external get_box: oct -> vnum = "ocaml_oct_get_box"
external from_box: vnum -> oct = "ocaml_oct_from_box"
external get_bounds: oct -> int -> num*num = "ocaml_oct_get_bounds"
external set_bounds: oct -> int -> num*num -> oct = "ocaml_oct_set_bounds"

(* preturbation *)
external add_epsilon: oct -> num -> oct = "ocaml_oct_add_epsilon"
external add_epsilon_max: oct -> num -> oct = "ocaml_oct_add_epsilon_max"
external add_epsilon_bin: oct -> oct -> num -> oct ="ocaml_oct_add_epsilon_bin"

(* utilities *)
external print: oct -> unit = "ocaml_oct_print"

(* minimal form *)
external m_to_oct: moct -> oct = "ocaml_oct_m_to_oct"
external m_from_oct: oct -> moct = "ocaml_oct_m_from_oct"
external m_print: moct -> unit = "ocaml_oct_m_print"
external m_dim: moct -> int = "ocaml_oct_m_dim"
external m_is_empty: moct -> bool = "ocaml_oct_m_is_empty"
external m_is_equal: moct -> moct -> bool = "ocaml_oct_m_is_equal"
external m_get_elem:  moct -> int -> int -> num = "ocaml_oct_m_get_elem"

(* top-level prettry printers *)
external elem_to_string: 
  oct -> int -> int -> string option = "ocaml_oct_elem_to_string"
external elem_to_string2: 
  oct -> int -> int -> string -> string option = "ocaml_oct_elem_to_string2"
external get_state: oct -> int = "ocaml_oct_get_state"

let foctprinter v f o =
  if (get_state o) = 0
  then Format.fprintf f "@[(empty)@]"
  else
    begin
      Format.fprintf f "@[";
(*      if (get_state o) = 2 then Format.fprintf f "(closed)@ ";*)
      Format.fprintf f "@[<hov 2>{@ ";

      let n = dim o in
      let beg = ref true in

      for i=0 to n-1 do
	if not (hastags o && (get_tag2 o (2*i+1) (2*i))) then
	  (match (elem_to_string2 o (2*i+1) (2*i) (v i)) with
	       Some a -> 
		 if !beg then beg:=false else Format.fprintf f ",@ ";
		 Format.fprintf f "@[%s@]" a
	     | _ -> ())
      done;

      for i=0 to n-1 do
	for j=0 to i-1 do
	  if not (hastags o && (get_tag2 o (2*j) (2*i))) then
	    (match (elem_to_string2 o (2*j) (2*i) ((v i)^"-"^(v j))) with
		 Some a ->
		   if !beg then beg:=false else Format.fprintf f ",@ ";
		   Format.fprintf f "@[%s@]" a
	       | _ -> ());
	  if not (hastags o && (get_tag2 o (2*j+1) (2*i))) then
	    (match (elem_to_string2 o (2*j+1) (2*i) ((v i)^"+"^(v j))) with
		 Some a ->
		   if !beg then beg:=false else Format.fprintf f ",@ ";
		   Format.fprintf f "@[%s@]" a
	       | _ -> ())
	done
      done;

      Format.fprintf f "@]@ }";

      if hastags o then
	begin
	  (* print_tags o; *)

	  Format.fprintf f " => @[<hov 2>{@ ";

	  beg := true;

	  for i=0 to n-1 do
	    if get_tag2 o (2*i+1) (2*i) then
	      (match (elem_to_string2 o (2*i+1) (2*i) (v i)) with
		   Some a -> 
		     if !beg then beg:=false else Format.fprintf f ",@ ";
		     Format.fprintf f "@[%s@]" a
		 | _ -> ())
	  done;

	  for i=0 to n-1 do
	    for j=0 to i-1 do
	      if get_tag2 o (2*j) (2*i) then
		(match (elem_to_string2 o (2*j) (2*i) ((v i)^"-"^(v j))) with
		     Some a ->
		       if !beg then beg:=false else Format.fprintf f ",@ ";
		       Format.fprintf f "@[%s@]" a
		   | _ -> ());
	      if get_tag2 o (2*j+1) (2*i) then
		(match (elem_to_string2 o (2*j+1) (2*i) ((v i)^"+"^(v j))) with
		     Some a ->
		       if !beg then beg:=false else Format.fprintf f ",@ ";
		       Format.fprintf f "@[%s@]" a
		   | _ -> ())
	    done
	  done;

	  Format.fprintf f "@]@ }"
	end;

      Format.fprintf f "@]"
    end


let octprinter v = foctprinter v Format.std_formatter

(* this version only prints the new version of changed constraints *)
let foctnewprinter v f o p =
  if dim o != dim p then failwith "oct_common.ml:foctnewprinter: incompatible octagon dimensions";
  if (get_state o) != (get_state p) then foctprinter v f p
  else if (get_state p) == 0 then Format.fprintf f "{@ }"
  else 
    begin
      Format.fprintf f "@[";
      Format.fprintf f "@[<hov 2>{@ ";

      let n = dim o in
      let beg = ref true in

      for i=0 to n-1 do
	if get_elem o (2*i+1) (2*i) <> get_elem p (2*i+1) (2*i) ||
	   get_elem o (2*i) (2*i+1) <> get_elem p (2*i) (2*i+1)
	then
	  (match (elem_to_string2 p (2*i+1) (2*i) (v i)) with
	    Some a -> 
	      if !beg then beg:=false else Format.fprintf f ",@ ";
	      Format.fprintf f "@[%s@]" a
	  | _ -> ())
      done;

      for i=0 to n-1 do
	for j=0 to i-1 do
	  if get_elem o (2*j) (2*i) <> get_elem p (2*j) (2*i) ||
             get_elem o (2*i) (2*j) <> get_elem p (2*i) (2*j)
	  then
	    (match (elem_to_string2 p (2*j) (2*i) ((v i)^"-"^(v j))) with
	      Some a ->
		if !beg then beg:=false else Format.fprintf f ",@ ";
		Format.fprintf f "@[%s@]" a
	    | _ -> ());
	  
	  if get_elem o (2*j+1) (2*i) <> get_elem p (2*j+1) (2*i) ||
             get_elem o (2*i) (2*j+1) <> get_elem p (2*i) (2*j+1) 
	  then
	    (match (elem_to_string2 p (2*j+1) (2*i) ((v i)^"+"^(v j))) with
	      Some a ->
		if !beg then beg:=false else Format.fprintf f ",@ ";
		Format.fprintf f "@[%s@]" a
	    | _ -> ())
	done
      done;
      
      Format.fprintf f "@]@ }@]"
    end

(** this version prints both the old and the new version of changed constraints
 *)
let foctdiffprinter v f o p =
  if dim o != dim p then failwith "oct_common.ml:foctdiffprinter: incompatible octagon dimensions";
  if (get_state o) != (get_state p) then Format.fprintf f "old:%a@ new:%a"
      (foctprinter v) o (foctprinter v) p
  else if (get_state p) == 0 then Format.fprintf f "{@ }"
  else 
    begin
      Format.fprintf f "@[";
      Format.fprintf f "@[<hov 2>{@ ";

      let n = dim o in
      let beg = ref true in

      let pp x y = match x,y with
	Some a,Some b -> 
	  if !beg then beg:=false else Format.fprintf f ",@ ";
	  Format.fprintf f "@[old: %s@ new: %s@]" a b
      | None,Some b -> 
	  if !beg then beg:=false else Format.fprintf f ",@ ";
	  Format.fprintf f "@[old: _@ new: %s@]" b
      | Some a,None -> 
	  if !beg then beg:=false else Format.fprintf f ",@ ";
	  Format.fprintf f "@[old: %s@ new: _@]" a
      | None,None -> ()
      in

      for i=0 to n-1 do
	if get_elem o (2*i+1) (2*i) <> get_elem p (2*i+1) (2*i) ||
	   get_elem o (2*i) (2*i+1) <> get_elem p (2*i) (2*i+1)
	then
	  pp (elem_to_string2 o (2*i+1) (2*i) (v i))
	     (elem_to_string2 p (2*i+1) (2*i) (v i))
      done;

      for i=0 to n-1 do
	for j=0 to i-1 do
	  if get_elem o (2*j) (2*i) <> get_elem p (2*j) (2*i) ||
             get_elem o (2*i) (2*j) <> get_elem p (2*i) (2*j)
	  then
	    pp (elem_to_string2 o (2*j) (2*i) ((v i)^"-"^(v j)))
	       (elem_to_string2 p (2*j) (2*i) ((v i)^"-"^(v j)));
	  
	  if get_elem o (2*j+1) (2*i) <> get_elem p (2*j+1) (2*i) ||
             get_elem o (2*i) (2*j+1) <> get_elem p (2*i) (2*j+1) 
	  then
	    pp (elem_to_string2 o (2*j+1) (2*i) ((v i)^"+"^(v j)))
	       (elem_to_string2 p (2*j+1) (2*i) ((v i)^"+"^(v j)))
	done
      done;
      
      Format.fprintf f "@]@ }@]"
    end

external melem_to_string: 
  moct -> int -> int -> string option = "ocaml_oct_melem_to_string"
external melem_to_string2: 
  moct -> int -> int -> string -> string option = "ocaml_oct_melem_to_string2"

let fmoctprinter v f o =
  if (m_is_empty o)
  then Format.fprintf f "@[(empty)@]"
  else
    begin
      Format.fprintf f "@[";
      Format.fprintf f "@[<hov 2>{@ ";

      let n = m_dim o in
      let beg = ref true in

       for i=0 to n-1 do
	(match (melem_to_string2 o (2*i+1) (2*i) (v i)) with
	  Some a -> 
	    if !beg then beg:=false else Format.fprintf f ",@ ";
	    Format.fprintf f "@[%s@]" a
	| _ -> ())
       done;
 
      for i=0 to n-1 do
	for j=0 to i-1 do
	  (match (melem_to_string2 o (2*j) (2*i) ((v i)^"-"^(v j))) with
	    Some a ->
	      if !beg then beg:=false else Format.fprintf f ",@ ";
	      Format.fprintf f "@[%s@]" a
	  | _ -> ());
	  (match (melem_to_string2 o (2*j+1) (2*i) ((v i)^"+"^(v j))) with
	    Some a ->
	      if !beg then beg:=false else Format.fprintf f ",@ ";
	      Format.fprintf f "@[%s@]" a
	  | _ -> ())
	done
      done;

      Format.fprintf f "@]@ }@]"
    end

let moctprinter v = fmoctprinter v Format.std_formatter

(* utilities *)
external memprint: unit -> unit = "ocaml_oct_memprint"
external timeprint: unit -> unit = "ocaml_oct_timeprint"

(* polyhedra <-> octagons conversion *)
(* 'a is used instead of Poly.t in case the Poly module is not defined *)
external from_poly: 'a -> oct = "ocaml_oct_from_poly"
external to_poly: oct -> 'a = "ocaml_oct_to_poly"
