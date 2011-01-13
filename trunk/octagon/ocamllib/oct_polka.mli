(* oct_polka.mli
   Polyhedra <-> octagons conversion

   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/
   
   Copyright (C) Antoine Mine' 2000-2002  
*)

external from_poly: Poly.t -> oct = "ocaml_oct_from_poly"
external to_poly: oct -> Poly.t = "ocaml_oct_to_poly"
