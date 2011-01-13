#include "bts0456.h"

/*@
 requires n>0;
 assigns \nothing;
 ensures \valid_range(\result,0,n-1);
*/
double *vecallocd(int n);

/*@
 assigns \nothing;
*/
void vecfreed(double *pd);

/*@
 requires (0<n) && \valid_range(my_bodies,0,n-1);
 assigns \nothing;
 ensures \valid_range(\result,0,n-1);
*/
value_type *cast_double_star(double *my_bodies, int n);

/*@
 assigns \nothing;
*/
value_type *cast_int(int n);

/*@
 assigns \nothing;
*/
value_type *cast_double(double n);



/*  This program computes the sum of the first n squares, for n>=0,
        sum = 1*1 + 2*2 + ... + n*n
    by computing the inner product of x=(1,2,...,n)^T and itself.
    The output should equal n*(n+1)*(2n+1)/6.
    The distribution of x is cyclic.
*/

//@logic integer nloc(int p, int s, int n) = (n+p-s-1)/p ;

/*@ lemma for_div_p :
@ \forall integer p, x; 0<p ==> 0<x ==> 0 < x/p <= x;
@*/

/*@ lemma div_p_help :
@ \forall integer p, x; 0<p ==> 0<x ==> x+p>x ==> x/p+1 == (x+p)/p;
@*/


/*@
 requires p==bsp_p && 0<=s<bsp_p && (bsp_p<n);
 assigns \nothing;
 ensures 0<\result<=n && \result==nloc(p,s,n);
*/
int nloc(int p, int s, int n)
{
    /* Compute number of local components of processor s for vector
       of length n distributed cyclically over p processors. */
    return  (n-s-1)/p+1 ; 
} /* end nloc */

/*@
 requires p==bsp_p && 0<=s<bsp_p && (bsp_p<n) && \valid_range(x,0,nloc(p,s,n)-1) && \valid_range(y,0,nloc(p,s,n)-1);
 assigns \nothing;
*/
double bspip(int p, int s, int n, double *x, double *y)
{
    /* Compute inner product of vectors x and y of length n>=0 */
    double inprod, *Inprod, alpha;
  
    Inprod=vecallocd(p);
    bsp_push_reg(cast_double_star(Inprod,p),p);
    bsp_sync();

    inprod= 0.0;
    
    /*@ loop variant nloc(p,s,n)-i; 
     loop invariant 0<=i<=nloc(p,s,n); 
    */    
    for (int i=0; i<nloc(p,s,n); i++){
        inprod += x[i]*y[i];
    }
    
    /*@ loop variant p-t; 
     loop invariant 0<=t<=p; 
    */
    for (int t=0; t<p; t++){
        bsp_put(t,cast_double(inprod),cast_double_star(Inprod,p),s,1);
    }
    bsp_sync();

    alpha= 0.0;
    
    /*@ loop variant p-t; 
     loop invariant 0<=t<=p; 
    */
    for (int t=0; t<p; t++){
        alpha += Inprod[t];
    }
    bsp_pop_reg(cast_double_star(Inprod,p));
    vecfreed(Inprod);
    return alpha;

} /* end bspip */


/*@
 requires bsp_p<n;
*/
void bspinprod(int n){
    double *x, alpha, time0, time1;
    int p, s, nl, iglob;
    
    p= bsp_nprocs(); /* p = number of processors obtained */ 
    s= bsp_pid();    /* s = processor number */ 

    bsp_push_reg(cast_int(n),1);
    bsp_sync();

    bsp_get(0,cast_int(n),0,cast_int(n),1);
    bsp_sync();
    bsp_pop_reg(cast_int(n));

    nl= nloc(p,s,n);
    x= vecallocd(nl);
      
    /*@ loop variant nl-i; 
     loop invariant 0<=i<=nl; 
    */
    for (int i=0; i<nl; i++){
        iglob = i*p+s;
        x[i] = iglob+1;
    }
    bsp_sync(); 
    time0=bsp_time();

    alpha= bspip(p,s,n,x,x);
    bsp_sync();  
    time1=bsp_time();

    vecfreed(x);
} /* end bspinprod */

/*@
 ensures bsp_p<\result;
 assigns \nothing;
*/
int atoi(char* arg);

/*@
requires argc==1 && \valid_range(argv,0,1);
assigns \nothing;
*/
int main(int argc, char **argv){
    int n;
 
    bsplib_init(&argc,&argv);
 
    n=(atoi(argv[1]));
 
    /* SPMD part */
    bspinprod(n);

    bsplib_done();

} /* end main */
