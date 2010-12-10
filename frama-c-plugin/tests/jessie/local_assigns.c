
#pragma SeparationPolicy(none)


typedef struct _my_type {int i; int j;} my_type;

/*@
 requires \valid(s);
 assigns s->i;
 ensures s->i == s->j;
*/
void my_changes (my_type* s){s->i = s->j;};

/*@
 assigns \result;
 ensures \result == n;
*/
int my_main (int n){
 my_type t;
 t.j=n;
 my_changes(&t);
 return t.i;
}
