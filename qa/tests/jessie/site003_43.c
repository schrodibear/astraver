
#define NMAX 3
#define NMAXR 3.0
#define VALUEMAX 100.0
//#define BOUND 0x1p-20 // Some VCs were not proved with this bound
#define BOUND 0x1p-15 

#define TRUE 1
#define FALSE 0
#define NACEL 3

/*@ axiomatic Sum {
  
  @   logic real sum{L}(float *x, integer n)
  @       reads x[..];

  @   axiom A1{L}: \forall float *x;
  @      sum(x,0) == 0.0;

  @   axiom A2{L}: \forall float *x; \forall integer n ;  n >= 0 ==>
  @        sum(x,n+1) == sum(x,n) + x[n];
  @ }
  @*/


/*@ lemma bound_int_to_real:
     \forall integer i; i <= NMAX ==> i <= NMAXR;
 @*/


float average, x[NACEL],p, Value;
unsigned char  pri, i;

int j;

struct
{
    unsigned int Ativo   : 1, /* evento ATIVO   */
                 Tratado : 1; /* evento TRATADO */
    float        Inst_Ativ;   /* tempo de ativacao do evento */
} Eventos[61];


/*@ requires 0 <= i <= NMAX - 1;
    requires \forall integer i; 0 <= i < NMAX ==> \abs(x[i]) <= VALUEMAX ;
    requires \abs(Value) <= VALUEMAX;
    ensures  (pri == 1)==>\abs(p - sum(x+0,NMAX)) <= NMAX * BOUND;
@*/
void test(unsigned char ID)
  {

 
  if((Eventos[7].Ativo == TRUE && Eventos[7].Tratado == FALSE))
    {
     pri = FALSE;
     i = 0;
     p = 0;
     }


  x[i] = Value;
  i = i + 1;
 
  if (i > NMAX - 1)
     {
     i = 0;
     pri = TRUE;
     }
 
  if (pri == TRUE)
  {
      p = 0;

/*@ loop invariant 0 <= j <= NMAX ;
    loop invariant \abs(sum(x+0,j)) <= VALUEMAX * j;
    loop invariant \abs(p - sum(x+0,j)) <= j * BOUND;
    loop variant NMAX-j;
@*/
    for(j=0;j<NACEL;j++)
    {
       L:
    // bounds, needed by Gappa
    //@ assert \abs(x[j]) <= VALUEMAX;
    //@ assert \abs(p) <= NMAXR*(VALUEMAX + BOUND) ;

        p = p + x[j];

    // bound on the rounding errors in the statement above, proved by gappa
    //@ assert \abs(p - (\at(p,L) + x[j])) <= BOUND;
     }
  
      average = p / NACEL;

      switch(ID)
      {
        case 1:
        if(Eventos[9].Ativo == FALSE)
        {
              if(average > 12.0)  
                {
                  Eventos[9].Ativo = TRUE;
                }
         }
         break;
         default:
         ;
       } 
  }
} 


