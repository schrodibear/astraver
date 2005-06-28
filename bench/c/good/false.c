
/* These programs _are_ incorrect i.e. the corresponding proof obligations
   should _not_ be provable.
   They are here to test the consistence of the theory. */

struct u{int x;};

struct v{struct u x; int y[5];};

struct v * z;
struct u zz;

int x[4];
int y[5];

/*@ ensures \false */
void false0() {
}

void false1() {
  z->y[5] = 3;
}

void false2() {
  x[-1] = 1;
}

void false3() {
  y[5] = 2;
}
