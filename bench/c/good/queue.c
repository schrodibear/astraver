
struct queue { 
  char *contents;
  int length;
  int first, last;
  unsigned int empty, full :1;
} q;

/*@ invariant q_invariant : 
  @   \valid_range(q.contents, 0, q.length-1) &&
  @   0 <= q.first < q.length &&
  @   0 <= q.last < q.length 
  @   (* && (q.full != 0 <=> q.last == q.first) *)
  @*/

/*@ requires !q.full
  @ assigns  q.empty, q.full, q.last, q.contents[q.last]
  @ ensures  !q.empty && q.contents[\old(q.last)] == c
  @*/
void push(char c) {
  q.contents[q.last++] = c;
  if (q.last == q.length) q.last = 0;
  q.empty = 0;
  q.full = q.first == q.last;
}

/* q.last = (q.last + 1) % q.length; BUG */

/*@ requires !q.empty
  @ assigns q.empty, q.full, q.first
  @ ensures !q.full && \result == q.contents[\old(q.first)]
  @*/
char pop() {
  char r = q.contents[q.first++];
  if (q.first == q.length) q.first = 0;
  q.full = 0;
  q.empty = q.first == q.last;
  return r;
}
