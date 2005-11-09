


/*@ requires size >= 0 && \valid_range(p,0,size-1)
  @ assigns p[0 .. size-1] */
void erase (int *p, int size){
  /*@ invariant 
    @   0 <= size <= \old(size) && p == \old(p)+(\old(size)-size)
    @ loop_assigns p[ 0 .. size-1]
    @ variant size
    @ 
    @*/
  while (size--) { *p=0; p++; }
}

