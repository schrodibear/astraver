void g( 
  int  Def_Rv 
  );


typedef struct SCONT 
{ 
  int        Def_Rv; 
} SCONT; 

/*@ requires Def_Rv == 1*/
void g( 
  int Def_Rv
); 

void g (int Def_Rv){
  Def_Rv = 1;
}







