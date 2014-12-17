
/*@ requires \valid(a+(0..len-1)) &&

  @         len >= 0 && len < 2147483647 &&

  @         0<=(len>>3L)<=len;

  @*/

void f(int *a,int len){

 

      int i = (int)(len>>3L);

      if(i>0) {
	//@ loop invariant i >= 1;
            while(1){

                  a+=8;

                  if(--i==0) break;

            }

      }

}
