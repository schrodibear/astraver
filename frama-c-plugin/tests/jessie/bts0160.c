typedef struct { int * rc; } S;
 
/*@
requires \valid(p)
  && \valid(p->rc)
  && \valid(r);
assigns *(\at(p->rc,Post)),p->rc;
*/
int main1(  S* p,int* r)
{
 p->rc = r;
 *(p->rc) = 55;
 return 1;
}
