
enum E1 { A1, B1 };
enum E2 { A2, B2, C2 };

/*@ requires e2 != C2 */
void f(enum E1 e1, enum E2 e2) {
  e1 = e2;
}

/*@ requires s <= 255 */
void g(unsigned short s) {
  char c = s;
}

void h() {
  char c = 10;
  unsigned char uc = c;
  char c1;
  short s = c1;
  int i = s;
  long int li = i;
  long long int lli = li;
}

void hh() {
  int i = 7;
  short s = i;
  char c = s;
}
