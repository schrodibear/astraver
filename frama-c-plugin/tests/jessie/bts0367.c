/* Frama-C BTS 0367

Status: solved


*/

#define bool_t int
#define float32_t float
#define TRUE 1

bool_t func1(float32_t x);
/*@ ensures \result == TRUE;
  
*/
bool_t func1(float32_t x)
 {
    if (x < 1E-6){
       ;
    }
   
    return TRUE;
}

/*
Local Variables:
compile-command: "make bts0367"
End:
*/
