
typedef float TYP ;

/*@ 

inductive incr{L}(TYP t[],integer i,integer j){

  case incr_ok{L}: 
    \forall TYP t[];\forall integer i,j; 
       i<j ==> t[i] <= t[i+1] ==> 
         incr{L}(t,i+1,j) ==> incr{L}(t,i,j);

  case incr_alone{L}: 
    \forall TYP t[];\forall integer i; incr{L}(t,i,i);
}

*/


/*@ predicate incr2{L}(TYP t[],integer i,integer j) =
  @   \forall integer k1,k2; i <= k1 <= k2 <= j ==> t[k1] <= t[k2]; 
  @*/

/*@ predicate incr3{L}(TYP t[],integer i,integer j) =
  @   \forall integer k; i <= k < j ==> t[k] <= t[k+1]; 
  @*/


void f()
{
  TYP t[20];
  // = {
  //  0.,1.,2.,3.,4.,5.,6.,7.,8.,9.,
  //  10.,11.,12.,13.,14.,15.,16.,17.,18.,19. };
  
  //@ assert t[0] == 0.;
  //@ assert t[1] == 1.;
  //@ assert t[2] == 2.;
  //@ assert t[3] == 3.;
  //@ assert t[4] == 4.;
  //@ assert t[5] == 5.;
  //@ assert t[6] == 6.;
  //@ assert t[7] == 7.;
  //@ assert t[8] == 8.;
  //@ assert t[9] == 9.;
  //@ assert t[10] == 10.;
  //@ assert t[11] == 11.;
  //@ assert t[12] == 12.;
  //@ assert t[13] == 13.;
  //@ assert t[14] == 14.;
  //@ assert t[15] == 15.;
  //@ assert t[16] == 16.;
  //@ assert t[17] == 17.;
  //@ assert t[18] == 18.;
  //@ assert t[19] == 19.;

  // @ assert incr(t,0,4);
  // @ assert incr(t,0,9);
  // @ assert incr(t,0,19);
  
  // @ assert incr2(t,0,4);
  // @ assert incr2(t,0,9);
  // @ assert incr2(t,0,19);
  
  //@ assert incr3(t,0,4);
  //@ assert incr3(t,0,9);
  //@ assert incr3(t,0,19);
  
}

/*
frama-c -jessie e63.c
*/
