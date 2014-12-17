
/*@ axiomatic Cpt {
  @
  @ logic integer cpt{L} (double *t,real u,integer d,integer f) reads t[..];
  @
  @ axiom c1{L} : \forall double *t, real u, integer i;
  @   i >= 0 && u >= t[i] ==>
  @     cpt{L}(t,u,0,i) == cpt{L}(t,u,0,i-1) + 1;
  @
  @ axiom c2{L} : \forall double *t, real u, integer i;
  @   i >= 0 && u < t[i] ==>
  @     cpt{L}(t,u,0,i) == cpt{L}(t,u,0,i-1);
  @
  @ axiom c3{L} : \forall double *t, real u, integer i;
  @   i < 0 ==> cpt{L}(t,u,0,i) == 0;
  @ }
  @*/


void NNN(float u,double t[5])
{
  int i;
  int tmp_1;

/*@ //GENA: annotations for loop (NNN.c:24)
loop invariant 0 <= i && i <= 5
  && (0 <= i && i <= 5 ==> 5 >= cpt{Here}(t,u,0,i-1));
loop assigns i, tmp_1;
loop variant 5 - i;
*/
  for (i = 0; i < 5; i++)
    {
          tmp_1 = 0;
    }

}
