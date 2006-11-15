
enum E { A = 1 , y = A + 3 };

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

// enum used as array index

enum I { U, V, W };

/*@ requires \valid_range(t, U, W)
  @ ensures  t[V] == 0
  @*/
void enum_as_array_index(int *t) {
  t[V] = 0;
}

