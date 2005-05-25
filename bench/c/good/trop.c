typedef struct las { int * p; int ta[1]; } las;

las u,v;

/*@
  requires \valid(u.p) && \base_addr(u.ta)!=\base_addr(u.p)
  assigns *u.p,u.ta[0]
  ensures u.ta[0]==0
*/
void f()
{
  //	g();
  u.ta[0]=0;
  *u.p=5;
}

