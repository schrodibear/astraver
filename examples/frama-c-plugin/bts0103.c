/* Frama-C BTS 0103

Status: closed

Fixed in Why 2.22: "loop variant 0" is added


*/


//@ requires \valid(p); assigns *p; ensures *p==4; 
void g(int*p){
    int i=0;
    while(1>0) { *p=3; }
}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0103.c"
End:
*/



