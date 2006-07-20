char c;
signed char sc;
char c1;
short s;

enum E1 { A1, B1 };
enum E2 { A2, B2, C2 };

enum E1 e1;
enum E2 e2;

/*@ requires e2 != C2 */
void f() {
  e1 = e2;
}

/*@ requires 0 <= s <= 255 */
void g() {
  c = s;
}

int i;
long int li;
long long int lli;

void h() {
  c = 10;
  sc = c;
  s = c1;
  i = s;
  li = i;
  lli = li;
}

void hh() {
  i = 7;
  s = i;
  c = s;
}
