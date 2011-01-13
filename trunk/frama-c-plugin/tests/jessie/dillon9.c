typedef struct { int * rc; } S;

/*@
requires \valid(p)
   && \valid(p->rc)
   && \valid(r);
assigns p->rc;
*/
int main1(  S* p,int* r)
{ int x;
  p->rc = &x;
  *(p->rc) = 55;
  return 1;
}
