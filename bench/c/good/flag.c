
/* Dijkstra's dutch flag */

typedef enum { BLUE = 1, WHITE = 2, RED = 3 } color;

color t[];
   
/*@ predicate isColor(int i) { i == BLUE || i == WHITE || i == RED }
  @*/

/*@ predicate isMonochrome(int i, int j, color c)
  @   { (*0 <= i && i <= j && j <= \length(t) *)
  @     \forall int k; i <= k && k < j => t[k] == c } 
  @*/

/*@ requires 0 <= i && i < \length(t) && 0 <= j && j < \length(t)
  @ assigns t[i],t[j]
  @ ensures 	  
  @   t[i] == \old(t[j]) && t[j] == \old(t[i])
  @*/
void swap(int i, int j);

/*@ requires 
  @   t != \null && n == \length(t) &&
  @   (\forall int k; 0 <= k && k < \length(t) => isColor(t[k]))
  @ assigns t[*]
  @ ensures 
  @   (\exists int b, int r; 
  @            isMonochrome(0,b,BLUE) &&
  @            isMonochrome(b,r,WHITE) &&
  @            isMonochrome(r,\length(t),RED))
  @*/
void flag(int n) {
  int b = 0;
  int i = 0;
  int r = n;
  /*@ invariant
    @   (\forall int k; 0 <= k && k < \length(t) => isColor(t[k])) &&
    @   0 <= b && b <= i && i <= r && r <= \length(t) &&
    @   isMonochrome(0,b,BLUE) &&
    @   isMonochrome(b,i,WHITE) &&
    @   isMonochrome(r,\length(t),RED)
    @ variant r - i
    @*/
  while (i < r) {
    switch (t[i]) {
    case BLUE:  
      swap(b, i);
      b++;
      i++;
      break;	    
    case WHITE: 
      i++; 
      break;
    case RED: 
      r--;
      swap(r, i);
      break;
    }
  }
}

