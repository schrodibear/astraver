/* Frama-C BTS 0073

Status: closed


*/


/*@
axiomatic myaxioms{

    predicate myrelation(int p,int q);
    logic int mylogic{L}(int * p);

    axiom myaxiom{L} :
    \forall int * p, q; \at(myrelation(mylogic(p),q),L);

}
@*/





/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0073.c"
End:
*/
