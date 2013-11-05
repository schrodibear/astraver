#define NUM 61
#define TRUE 1
#define FALSE 0

struct{
     unsigned int Gbl_A   :1,
                  Gbl_T   :1;
     float Gbl_I;
}Gbl_E[NUM];

int a, a1, b, b1, c, c1, d, d1, e, e1, f, f1, g, g1;
unsigned char mode1;
unsigned long int flag, time1;

/*@ requires 0.0 <= time1 <= 3840; 
*/
void Event(void)
{
   switch(mode1)
   {
   case 1:
               if(a == TRUE && a1 == FALSE)
               {
		 flag = time1;
               }
	                      
               if(b == TRUE && b1 == FALSE)
               {
		  Gbl_E[0].Gbl_T = TRUE;
           	  flag = 1;
               }
	       
               if(c == TRUE && c1 == FALSE)
               {
                  flag = 2;
               }  
	     
	      if(d == TRUE && d1 == FALSE)
              {
                 Gbl_E[60].Gbl_T = TRUE; 
                 flag = 3;
              }
	      
              if(e == TRUE && e1 == FALSE)
              {
                flag = 4;
              }
              if(f == TRUE && f1 == FALSE)
              {
                  flag = 5;
              }
              if(g == TRUE && g1 == FALSE)
              {
                  flag = 6;
              }
        break;
    }
}
