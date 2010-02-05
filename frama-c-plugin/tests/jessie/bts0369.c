/* Frama-C BTS 0369


Status: open

*/

#pragma JessieIntegerModel(exact)

typedef struct qr { int q; int r; } qr;

// md is a recursive function
/*@ requires d>0 && n>=0;
  @ decreases n;
  @*/
qr md(int n,int d){ 
  int q,r; qr v;
  if (n==0) { 
    v.q = 0;
    v.r = 0;
    return v;
  } 
  else { 
    v = md(n-1,d);
    return v;
  }
}


/*
Local Variables:
compile-command: "make bts0369"
End:
*/
