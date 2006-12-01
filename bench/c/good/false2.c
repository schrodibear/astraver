
int e;

/*@ assigns e
  @ ensures e == 0
  @*/
void f();

/*@ ensures e == 1
  @*/
int main() {
  e=1;
  f();
  return 0;
}
