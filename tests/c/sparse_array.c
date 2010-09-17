
typedef unsigned int uint;

#define MAXLEN 1000

typedef struct SparseArray {
  int val[MAXLEN];
  uint idx[MAXLEN], back[MAXLEN];
  uint n;
  uint sz;
} *sparse_array;

/*@ requires sz <= MAXLEN;
  @ // ensures \fresh(\result);
  @*/
sparse_array create(uint sz) {
  sparse_array a = (sparse_array)malloc(sizeof(struct SparseArray));
  a->n = 0;
  a->sz = sz;
  return a;
}

/*@ requires \valid(a);
  @*/
int get(sparse_array a, uint i) {
  if (a->idx[i] < a->n && a-> back[a->idx[i]] == i) return a->val[i];
  else return 0;
}

/*@ requires \valid(a);
  @*/
void set(sparse_array a, uint i, int v) {
  a->val[i] = v;
  if (!(a->idx[i] < a->n && a-> back[a->idx[i]] == i)) {
    //@ assert a->n < MAXLEN;
    a->idx[i] = a->n; a->back[a->n] = i; a->n++;
  }
}



int main() {
  sparse_array a = create(10), b = create(20);
  int x,y;
  x = get(a,5); y = get(b,7);
  //@ assert x == 0 && y == 0;
  set(a,5,1); set(b,7,2);
  x = get(a,5); y = get(b,7);
  //@ assert x == 1 && y == 2;
  x = get(a,0); y = get(b,0);
  //@ assert x == 0 && y == 0;
  return 0;
}




