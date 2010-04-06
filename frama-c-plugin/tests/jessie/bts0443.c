/* Frama-C BTS 0443

Status: open, major bug

no VC are generated, although the assigns clause is wrong
  
*/

# pragma SeparationPolicy(regions)

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



