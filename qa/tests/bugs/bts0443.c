/* Frama-C BTS 0443

Status: closed

no VC were generated, although the assigns clause is wrong
  
*/

// # pragma SeparationPolicy(none)

int a[1];

//@ assigns \nothing;
void f(void) {
    a[0] = 3;
}


/* 
Local Variables:
compile-command: "make bts0443"
End:
*/



