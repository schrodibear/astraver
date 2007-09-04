
void loop1(int n) {
  //@ variant n
  while (n > 0) n--;
}

void loop2(int n) {
  //@ variant 100-n
  while (n < 100) n++;
}

//@ ensures \result == 0
int loop3() {
  int i = 100;
  //@ invariant 0 <= i variant i
  while (i > 0) i--;
  return i;
}

//@ ensures \result == 100
int sum() {
  int i = 100, s;
  //@ invariant 0 <= i <= 100 && s == 100-i variant i
  for (s = 0; i > 0; i--) s++;
  return s;
} 


//@ requires 0 <= n
void loop(int n) {
  int i;
  //@ invariant 0 <= i <= n variant n-i
  for (i = 0; i < n; i++);
}

