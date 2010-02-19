/* Frama-C BTS 0406


Status: fixed

*/



/*@ axiomatic U { axiom toto :
  @ \forall double f; 0x1p-1022 <= \abs(f) || \abs(f) < 0x1p-1022; }
  @*/
