typedef struct {int a;int b;} lastruct1; 
typedef struct {lastruct1 c;int d;} lastruct2; 
lastruct2 ls = {{1,2},3}; 

int varglo=123; 


typedef enum 
{ 
 a = 12, 
 b = 34, 
 c = 56 
} lenum;

 
lenum le=b; 


const int laconstante=7; 


/*@ 
assigns \nothing 
ensures  ls.c.a==1 && varglo==123 &&  \result==4  && le==34  
   && laconstante==7 
*/ 
int f() 
{ 
  int varloc=4; 
  return varloc;  

}
