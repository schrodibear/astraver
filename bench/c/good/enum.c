
enum E { x = 1 , y = x + 3 };

/*@ ensures y == 4 */
void f() { }

/*@ ensures 1 <= \result <= 4 */
int g(enum E e) { return e; }

typedef enum { BLUE, WHITE, RED } color;

/*@ requires \valid_range(t,0,9)
  @ ensures t[2] == BLUE || t[2] == WHITE || t[2] == RED 
  @*/
void h(color *t) { 
  t[2] = t[0];
}
