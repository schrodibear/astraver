/* Frama-C BTS 0073

File "jc/jc_separation.ml", line 96, characters 28-28:
Uncaught exception: File "jc/jc_separation.ml", line 96, characters 28-34: Assertion failed


Status: reopened


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
compile-command: "make bts0073"
End:
*/
