int v; 
/*@ ghost int pre_v */ 
/*@ ghost int pre2_v */ 

/*@ 
assigns v 
ensures v==-\old(v) 
*/ 
void g(){ v = -v; } 


/*@ 
assigns v,pre_v,pre2_v 
*/ 
void f() 
{ 
  int n; 
  
  n=100; 
  /*@ set pre2_v = 5 */ 
  /*@ set pre_v = -5 */ 
  v=5; 
  
  
  /*@ 
    invariant 0<=n<=100 && (pre2_v > pre_v => pre_v < v) && (pre_v == -v) 
    loop_assigns v,pre_v,pre2_v 
    variant n 
  */ 
  while(n--) 
    { 
      /*@ set pre2_v = pre_v */ 
      /*@ set pre_v = v */ 
      g(); 
    } 
}
