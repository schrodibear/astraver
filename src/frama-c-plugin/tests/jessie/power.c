


/*@ axiomatic PowerInt {
      logic real power(real x, integer n);
      }
*/
#pragma JessieBuiltin(power, "\\real_int_pow")

/*@ lemma L: power(2.0,2) == 4.0;
 */
