
/* borrowed from frama-c/tests/spec/model*.c */

struct S;

/*@ model struct S { integer foo; }; */

/*@ 
  requires \valid(s);
  assigns *s;
  ensures s->foo == 0;
*/
void reset (struct S* s);

/*@ 
  requires \valid(s);
  assigns *s;
  ensures s->foo > \at(s->foo,Pre);
*/
void inc(struct S* s);

/*@ 
  requires \valid(s);
  assigns *s;
  ensures s->foo < \at(s->foo,Pre);
*/
void dec(struct S* s);

/*@  
  requires \valid(s);
  assigns \nothing;
  behavior is_true:
  assumes s->foo > 0;
  ensures \result == 1;
  behavior is_false:
  assumes s->foo <= 0;
  ensures \result == 0;
*/
int is_pos(struct S* s);

void test (struct S *s) {
  reset(s);
  inc(s);
  /*@ assert s->foo > 0; */
  /*@ loop variant s->foo; */
  while (is_pos(s)) dec(s);
  /*@ assert s->foo <= 0; */
}


/* "implementation" */
  

struct S { int bar; };

/* type invariant foobar(struct S *s) = s->bar == s->foo; */

void reset (struct S* s) { s->bar == 0; }

void inc(struct S* s) { s->bar += 5; }

void dec(struct S* s) { s->bar--; }

int is_pos (struct S* s) { return (s->bar > 0) ? 1 : 0; }


