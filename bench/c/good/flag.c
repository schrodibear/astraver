
/* Dijkstra's dutch flag */

/* en attente de interp
typedef enum { BLUE, WHITE, RED } color;
*/

typedef enum { aBLUE, aWHITE, aRED } color;

color BLUE;
color WHITE;
color RED;

/*@ predicate isColor(int i) { i == BLUE || i == WHITE || i == RED }
  @*/

/*@ predicate isMonochrome(int t[], int i, int j, color c)
  @   { \valid_range(t,i,j) && \forall int k; i <= k && k < j => t[k] == c } 
  @*/

/*@ requires \valid_index(t,i) && \valid_index(t,j)
  @ assigns t[i],t[j]
  @ ensures t[i] == \old(t[j]) && t[j] == \old(t[i])
  @*/
void swap(int t[], int i, int j);

/*@ requires 
  @   \valid_range(t,0,n) &&
  @   (\forall int k; 0 <= k && k < n => isColor(t[k]))
  @ assigns t[0 .. n]
  @ ensures 
  @   (\exists int b, int r; 
  @            isMonochrome(t,0,b,BLUE) &&
  @            isMonochrome(t,b,r,WHITE) &&
  @            isMonochrome(t,r,n,RED))
  @*/
void flag(int t[], int n) {
  int b = 0;
  int i = 0;
  int r = n;
  /*@ invariant
    @   (\forall int k; 0 <= k && k < n => isColor(t[k])) &&
    @   0 <= b && b <= i && i <= r && r <= n &&
    @   isMonochrome(t,0,b,BLUE) &&
    @   isMonochrome(t,b,i,WHITE) &&
    @   isMonochrome(t,r,n,RED)
    @ variant r - i
    @*/
  while (i < r) {
    /* en attente de l'interp du switch 
    switch (t[i]) {
    case BLUE:  
      swap(t, b++, i++);
      break;	    
    case WHITE: 
      i++; 
      break;
    case RED: 
      swap(t, --r, i);
      break;
    }
    */
    if (t[i] == BLUE) swap(t, b++, i++);
    else if (t[i] == WHITE) i++; 
    else if (t[i] == RED) swap(t, --r, i);
  }
}

