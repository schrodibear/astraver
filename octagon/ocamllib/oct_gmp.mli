(* oct_gmp.mli
   Underlying numerical domains using GMP.

   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/
   
   Copyright (C) Antoine Mine' 2000-2002  
*)

external num_of_mpz: Gmp.Z.t -> num = "ocaml_num_mpz"
external num_of_mpq: Gmp.Q.t -> num = "ocaml_num_mpq"
external num_of_mpfr: Gmp.FR.t -> num = "ocaml_num_mpfr"

external vnum_of_mpz: Gmp.Z.t array -> vnum = "ocaml_vnum_mpz"
external vnum_of_mpq: Gmp.Q.t array -> vnum = "ocaml_vnum_mpq"
external vnum_of_mpfr: Gmp.FR.t array -> vnum = "ocaml_vnum_mpfr"

external vnum_of_mpz_opt: Gmp.Z.t option array -> vnum = "ocaml_vnum_mpz_opt"
external vnum_of_mpq_opt: Gmp.Q.t option array -> vnum = "ocaml_vnum_mpq_opt"
external vnum_of_mpfr_opt: Gmp.FR.t option array -> vnum = "ocaml_vnum_mpfr_opt"

external mpz_of_num: num -> Gmp.Z.t option = "ocaml_mpz_num"
external mpq_of_num: num -> Gmp.Q.t option = "ocaml_mpq_num"
external mpfr_of_num: num -> Gmp.FR.t option = "ocaml_mpfr_num"

external mpz_of_vnum: vnum -> Gmp.Z.t option array = "ocaml_mpz_num"
external mpq_of_vnum: vnum -> Gmp.Q.t option array = "ocaml_mpq_num"
external mpfr_of_vnum: vnum -> Gmp.FR.t option array = "ocaml_mpfr_num"


