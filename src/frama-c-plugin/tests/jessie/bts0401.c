/* Frama-C BTS 0401

(clash with case names and predicate)

Status: closed


*/

 /*@ predicate foo(integer x) = \true;
   
   inductive bar(integer x) {
   case foo: \forall integer x; foo(x) ==> bar(x);
   }
   
   lemma test: \forall integer x; bar(x);
   */


/*
Local Variables:
compile-command: "make bts0401"
End:
*/
