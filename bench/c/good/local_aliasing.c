
/* test option --local-aliasing */

extern char* name ;
//@ axiom name_valid : \valid_range(name,0,99)

//@ requires \valid_range(buf,0,size-1) && 0 <= size <= 100
int f(char* buf, int size) {
  int i;
  char* p = buf;
  char* q = name;
  /*@ invariant 0 <= size <= \old(size)
    @           && p-buf == \old(size)-size
    @           && q-name == \old(size)-size
    @*/
  while (size--) {
    *p++ = *q++;
  }
  if (q == name) return 1;
  --buf;
  /*@ invariant 0 <= i <= \old(size)
    @*/
  for (i = p-buf-2; i> 1; i--) {
    buf[i] += 2;
  }
  ++buf;
  return 0;
}

//@ requires \exists int i; i >= 0 && s[i] == 0 && \valid_range(s,0,i)
int g(char* s) {
  char c;
  int count = 0;
  /*@ invariant \exists int i; i >= 0 && s[i] == 0 && \valid_range(s,0,i)
    @*/
  while (c = *s++) {
    switch (c) {
    case '0':
    case '1':
      count += 1;
      break;
    case '2':
      count -= count;
      if (!*s++) s--;
//  case '3':
    default:
      ++count;
      if (!*s++) s--;
      if (!*s++) s--;
    }
  }
  return count;
}

int h(char* p, int s) {
  char *q = p+s;
  char *pp = p;
  char buf[100];
  char *b = buf;
  //@ assert b == buf
  pp++;
  //@ assert pp == p + 1
  ++b;
  //@ assert b == buf + 1
  if (p < q && buf < b) {
    int diff = (buf-b) + (pp-p);
    diff += (q-p);
    //p = malloc(100 * sizeof(char));
    p++;
    //@ assert pp == p
    pp++;
    //@ assert pp == p + 1
    q++;
    //@ assert pp + s == q + 1
    diff += (q-pp);
    q = (char*)malloc(100 * sizeof(char));
    p = pp;
    //@ assert pp == p
    diff += (p-pp);
    return diff;
  }
  return -1;
}

int main() {
  char buf[100];
  int r = f(buf,100);
  buf[99] = 0;
  r += g(buf);
  r += h(buf,100);
  return r;
}
