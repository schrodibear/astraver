/*@ ensures x==4 => \result==2 */
int f1 (int x){
  int y ;
  
  switch (x) {
  case 0 :
  case 1 : 
    y=1 ;
    y=4;
    break;
  case 2:
  case 4:
    y=2; break;
  case 3:
    y=3; break;
  default :
    y=4;
    y=5;
  }
  return y;
}

/*@ ensures x==4 => \result==2 */
int f1a (int x){
  int y ;
  
  switch (x) {
  case 0 :
  case 1 : 
    y=1 ;
    y=4;
    break;
  case 2:
  case 4:
    y=2; return y;
  case 3:
    y=3; return y;
  default :
    y=4;
  }
  y=5;
  return y;
}

/*@ ensures \result==4 */
int f2 (int x){
  int y ;
  
  switch (x) {
  case 0 :
  case 1 : 
    y=1 ;
  case 2:
  case 4:
    y=2;
  case 3:
    y=3;
  default :
    y=4;
  }
  return y;
}

/*@ ensures \result==4 */
int f3 (int x){
  int y;

  switch (x) { 
  case 0 :
  case 1 : 
    y=1 ;
  default :
    y=2;
  case 3 :
    y=3;
  case 2 :
    y=4;
  }
  return y;
}

/*@ ensures \result==0 */
int f4 (int x){
  int y = 0;

  switch (x) { 
  case 0 :
    if (x==0) break ;
    y = 1;
  }
  return y;
}

/*@ ensures x==1 => \result==1 */
int f5 (int x){
  int y = 0;

  switch (x) { 
  case 1 :
    while (x>0) break ;
    y = 1;
  }
  return y;
}


