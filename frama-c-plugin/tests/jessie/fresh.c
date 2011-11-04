



/*@ assigns \nothing;
  @ ensures \valid(\result) && \fresh(\result);
  @*/
int* f();


void g() {
   int* p;
   p = f();
   *p = 0;
}
