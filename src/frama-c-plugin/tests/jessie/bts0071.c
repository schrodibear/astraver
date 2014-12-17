/* Frama-C BTS 0071 

Status: closed

yields:

File "why/label.why", line 350, characters 30-47:
Unbound label 'Mylabel'


Fixed in Why 2.20

*/

void myfun(int p){
    p = 1;
    //@ ghost Mylabel:
    p = 2;
    //@ assert \at(p,Mylabel)==p-1;
}

/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0071.c"
End:
*/
