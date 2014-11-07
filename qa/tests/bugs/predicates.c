
/*@
 axiomatic _1 {
    predicate p1 (integer a) = a > 0;
    predicate p4 (integer a) = a > 0 ? \true : \false;
    logic boolean p2 (integer a) = a > 0;
    logic boolean p3 (integer a) = a > 0 ? \true : \false;
 }
*/ 

//@ requires p2(arg);
int a (int arg)
{
}

